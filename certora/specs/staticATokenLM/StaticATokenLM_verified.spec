import "StaticATokenLM_base.spec"

/////////////////// METHODS ////////////////////////

    methods
    {   
        getReserveData_isActive() returns (bool) envfree
        getReserveData_isPaused() returns (bool) envfree
        getReserveData_isFrozen() returns (bool) envfree

        getClaimableRewards(address, address) returns (uint256)
        saveCastToUint128(uint256) returns (uint128) envfree

        mint(uint256, address) returns (uint256)
        deposit(uint256, address, uint16, bool) returns (uint256)
        deposit(uint256, address) returns (uint256)
        withdraw(uint256, address, address) returns (uint256)
        redeem(uint256, address, address) returns (uint256)

        convertToShares(uint256) returns (uint256)
        convertToAssets(uint256) returns (uint256)
        maxRedeemUnderlying(address) returns (uint256)
        maxDepositUnderlying(address) returns (uint256)

        metaDeposit(address, address, uint256, uint16, bool, uint256, (address, address, uint256, uint256, uint8, bytes32, bytes32), (uint8, bytes32, bytes32)) returns (uint256)
        metaWithdraw(address, address, uint256, uint256, bool, uint256, (uint8, bytes32, bytes32)) returns (uint256, uint256)
    }

///////////////// DEFINITIONS //////////////////////

    /// @notice Protocol is paused, should have `PAUSED` flag or not have `ACTIVE` flag 
    definition isPaused() returns bool = getReserveData_isPaused() || !getReserveData_isActive();

    /// @notice Protocol is frozen, should have `FROZEN` flag
    definition isFrozen() returns bool = getReserveData_isFrozen();

    definition maxUnderlyingFunctions(method f) returns bool = (
        f.selector == maxRedeemUnderlying(address).selector 
        || f.selector == maxDepositUnderlying(address).selector
        );
    
    definition metaFunctions(method f) returns bool = (
        f.selector == metaDeposit(address, address, uint256, uint16, bool, uint256, (address, address, uint256, uint256, uint8, bytes32, bytes32), (uint8, bytes32, bytes32)).selector 
        || f.selector == metaWithdraw(address, address, uint256, uint256, bool, uint256, (uint8, bytes32, bytes32)).selector 
        );

    /// @notice `metaDeposit()` is excluded because of the off-chain cryptography
    definition mintFunctions(method f) returns bool = (
        f.selector == deposit(uint256, address, uint16, bool).selector 
        || f.selector == deposit(uint256, address).selector
        || f.selector == mint(uint256, address).selector
        );
    
    /// @notice `metaWithdraw()` is excluded because of the off-chain cryptography 
    definition burnFunctions(method f) returns bool = (
        f.selector == withdraw(uint256, address, address).selector 
        || f.selector == redeem(uint256, address, address).selector
        );

    definition transferFunctions(method f) returns bool = (
        f.selector == transfer(address, uint256).selector 
        || f.selector == transferFrom(address, address, uint256).selector
        );

    definition ray() returns uint = 1000000000000000000000000000;
    definition half_ray() returns uint = ray() / 2;
    definition bound() returns uint = ((gRNI() / ray()) + 1 ) / 2;
    /// @notice Due to rayDiv and RayMul Rounding (+ 0.5) - blance could increase by (gRNI() / Ray() + 1) / 2.
    definition bounded_error_eq(uint x, uint y, uint scale) returns bool = x <= y + (bound() * scale) && x + (bound() * scale) >= y;

////////////////// FUNCTIONS //////////////////////

    /// @notice summerization for scaledBlanaceOf -> regularBalanceOf + 0.5 (canceling the rayMul)
    ghost gRNI() returns uint256 {
        axiom gRNI() == 7 * ray();
    }

    /// @notice Setup user assumptions
    function setupUser(env e, address user)
    {
        require user != 0;
        require currentContract != e.msg.sender;
        require currentContract != user;
        require _AToken != user;
        require _RewardsController !=  user;
        require _DummyERC20_aTokenUnderlying  != user;
        require _DummyERC20_rewardToken != user;
        require _SymbolicLendingPool != user;
        require _TransferStrategy != user;
        require _TransferStrategy != user;
    }

    /// @notice Setup reward token assumptions
    function setupEnv(env e)
    {
        require getRewardTokensLength() > 0;
        require _RewardsController.getAvailableRewardsCount(_AToken)  > 0;
        require _RewardsController.getRewardsByAsset(_AToken, 0) == _DummyERC20_rewardToken;
        require getReserveData_AToken() == _AToken;

        single_RewardToken_setup();

        require _SymbolicLendingPool.getReserveNormalizedIncome(e, getStaticATokenUnderlying()) == 2 
            || _SymbolicLendingPool.getReserveNormalizedIncome(e, getStaticATokenUnderlying()) == 1;
    }

///////////////// PROPERTIES ///////////////////////

    /**
    * @notice Prove "certora/bug1.patch"
    * Variable Transition: check if `unclaimedRewards` is updated correctly 
    **/
    rule updateUserUnclaimedRewards(env e, address user1, address user2) {
        setupUser(e, user1);
        setupUser(e, user2);
        require e.msg.sender == user1;
        require user1 != user2;

        setupEnv(e);
        address rewardToken;
        require rewardToken == _DummyERC20_rewardToken;

        // Updating of `unclaimedRewards` requires the user's balance > 0
        require balanceOf(user1) != 0;
        require balanceOf(user2) != 0;

        // Precalculate `_getClaimableRewards()` call in `_updateUser()`
        mathint claimableRewards1 = saveCastToUint128(getClaimableRewards(e, user1, rewardToken));
        mathint claimableRewards2 = saveCastToUint128(getClaimableRewards(e, user2, rewardToken));

        // Transfer `amount` from `user1` to `user2` to execute `_beforeTokenTransfer()` 
        uint256 amount;
        transfer(e, user2, amount);

        // `_beforeTokenTransfer()` should change the users's `unclaimedRewards` the same way
        mathint unclaimedRewards1 = saveCastToUint128(getUnclaimedRewards(user1, rewardToken));
        assert unclaimedRewards1 == claimableRewards1; 
        mathint unclaimedRewards2 = saveCastToUint128(getUnclaimedRewards(user2, rewardToken));
        assert unclaimedRewards2 == claimableRewards2; 
    }
    
    /**
    * @notice Prove "certora/bug6.patch"
    * Unit test: minted `assets` should be calculated based on `shares` 
    **/
    rule mintAssetsBasedOnPreviewMint(env e, address user1, address user2) {
        setupUser(e, user1);
        setupUser(e, user2);
        require e.msg.sender == user1;
        require user1 != user2;

        uint256 shares;
        mathint assets = mint(e, shares, user2);

        // Amount of minted assets should be calculated based on `shares`
        assert assets == previewMint(e, shares);
    }
    
    /**
    * @notice Prove "certora/bug9.patch"
    * Unit test: `maxRedeemUnderlying()` should return up to the available amount 
    **/
    rule maxRedeemUnderlyingResult(env e, address user) {
        setupUser(e, user);
        setupEnv(e);

        // Assume the protocol has `ACTIVE` and has not `PAUSED` flags
        require !isPaused();

        mathint userBalance = balanceOf(user);
        mathint underlyingTokenBalanceInShares = convertToShares(
            e,
            _DummyERC20_aTokenUnderlying.balanceOf(_AToken)
        );

        mathint amount = maxRedeemUnderlying(e, user);
        
        // Users can withdraw up to the available amount
        assert amount == (
            underlyingTokenBalanceInShares >= userBalance 
            ? userBalance 
            : underlyingTokenBalanceInShares
            );
    }

    /**
    * @notice Prove "participants/bug1.patch"
    * High-level: could not get max underlying value when paused or frozen (for deposit) 
    **/
    rule forbidMaxUnderlyingValueWhenPaused(env e, method f, address user) 
        filtered { f -> maxUnderlyingFunctions(f) } {

        uint256 result;

        setupUser(e, user);

        // `maxRedeemUnderlying()`: the protocol has `PAUSED` flag or has not `ACTIVE` flag 
        if(f.selector == maxRedeemUnderlying(address).selector) {
            require isPaused();
            result = maxRedeemUnderlying(e, user);
        // `maxDepositUnderlying()`: additionally or assume the protocol could have `FROZEN` flag
        } else { // if(f.selector == maxDepositUnderlying(address).selector) {
            require isPaused() || isFrozen();
            result = maxDepositUnderlying(e, user);
        } 

        // Always return zero when paused
        assert result == 0;
    }
        
    /**
    * @notice Prove "participants/bug2.patch"
    * Valid state: total supply is the summary of tokens of all users
    **/
    invariant balanceSolvency() totalSupply() == sumAllBalance() 
        filtered { f -> !f.isView && !harnessOnlyMethods(f) && !metaFunctions(f) } {
        preserved with(env e) {
            require e.msg.sender != currentContract;
        }
    }

    /**
    * @notice Prove "participants/bug3.patch"
    * State transition: each possible operation changes the balance of at most two users
    **/
    rule balanceOfChangeMaxTwoUsers(env e, method f, address user1, address user2, address user3) 
        filtered { f -> !f.isView && !harnessOnlyMethods(f) && !metaFunctions(f) } {

        setupUser(e, user1);
        setupUser(e, user2);
        setupUser(e, user3);

        require user1 != user2 && user1 != user3 && user2 != user3;

        uint256 balance1Before = balanceOf(user1);
        uint256 balance2Before = balanceOf(user2);
        uint256 balance3Before = balanceOf(user3);
        
        calldataarg arg;
        f(e, arg); 

        uint256 balance1After = balanceOf(user1);
        uint256 balance2After = balanceOf(user2);
        uint256 balance3After = balanceOf(user3);

        // At least one user's balance should not changed
        assert (balance1Before == balance1After 
            || balance2Before == balance2After 
            || balance3Before == balance3After
            );
    }

    /**
    * @notice Prove "participants/bug4.patch"
    * Hight level: could not get zero tokens when depositing or minting
    **/
    rule mintNotZeroAmount(env e, method f, address caller) 
        filtered { f -> mintFunctions(f) } {
        uint256 minted;
        uint256 amount;
        address recipient;

        setupUser(e, caller);
        setupUser(e, recipient);
        require e.msg.sender == caller;
        require caller != recipient;

        setupEnv(e);

        if(f.selector == deposit(uint256, address, uint16, bool).selector) {
            uint16 referralCode;
            bool fromUnderlying;
            minted = deposit@withrevert(e, amount, recipient, referralCode, fromUnderlying);
        } else if (f.selector == deposit(uint256, address).selector) {
            minted = deposit@withrevert(e, amount, recipient);
        } else { // if (f.selector == mint(uint256, address).selector) {
            minted = mint@withrevert(e, amount, recipient);
        }

        // Should not return zero in any case
        assert minted == 0 => lastReverted;
    }
    
    /**
    * @notice Prove "participants/bug5.patch"
    * Variable Transition: mint correctly increases the total supply of shares
    **/
    rule mintIncreasesSharesTotalSupply(env e, address caller, uint256 shares, address recipient) {
        setupUser(e, caller);
        setupUser(e, recipient);
        require e.msg.sender == caller;
        require caller != recipient;

        setupEnv(e);

        uint256 sharesBalanceBefore = balanceOf(recipient);
        uint256 totalSharesBefore = totalSupply();
        require sharesBalanceBefore <= totalSharesBefore;

        mint(e, shares, recipient);

        uint256 sharesBalanceAfter = balanceOf(recipient);
        uint256 totalSharesAfter = totalSupply();

        // Total shares increasing the same amount as user's shares
        assert totalSharesAfter > totalSharesBefore;
        assert totalSharesAfter - totalSharesBefore == sharesBalanceAfter - sharesBalanceBefore;
    }
    
    /**
    * @notice Prove "participants/bug6.patch"
    * Variable Transition: mint correctly increases the total supply of underlying assets
    **/
    rule mintIncreasesAssetsTotalSupply(env e, address caller, uint256 shares, address recipient) {
        setupUser(e, caller);
        setupUser(e, recipient);
        require e.msg.sender == caller;
        require caller != recipient;

        setupEnv(e);

        uint256 totalAssetsBefore = totalAssets(e);
        uint256 assets = previewMint(e, shares);

        mint(e, shares, recipient);

        uint256 totalAssetsAfter = totalAssets(e);

        // Total underlying assets increasing the same amount as underlying increased assets 
        assert bounded_error_eq(totalAssetsAfter, totalAssetsBefore + assets, 1);
    }

    /**
    * @notice Prove "participants/bug7.patch"
    * State transition: mint increases recipient balance
    **/
    rule mintIncreasesRecipientBalance(env e, address caller, address recipient) {
        setupUser(e, caller);
        setupUser(e, recipient);
        require e.msg.sender == caller;
        require caller != recipient;

        setupEnv(e);

        uint256 recipientBalanceBefore = balanceOf(recipient);

        uint256 shares;
        mint(e, shares, recipient);

        uint256 recipientBalanceAfter = balanceOf(recipient);

        // Increases recipient balance
        assert recipientBalanceAfter > recipientBalanceBefore 
            => recipientBalanceAfter - recipientBalanceBefore == shares;
    }

    /**
    * @notice Prove "participants/bug8.patch"
    * Hight level: mint doesn't touch other balances
    **/
    rule mintTouchOnlyRecipientBalance(env e, address caller, uint256 shares, address recipient) {
        setupUser(e, caller);
        setupUser(e, recipient);
        require e.msg.sender == caller;
        require caller != recipient;

        address other;
        setupUser(e, other);
        require other != caller && other != recipient;

        setupEnv(e);

        uint256 callerBalanceBefore = balanceOf(caller);
        uint256 otherBalanceBefore = balanceOf(other);

        mint(e, shares, recipient);

        uint256 callerBalanceAfter = balanceOf(caller);
        uint256 otherBalanceAfter = balanceOf(other);

        // Don't touch other balances
        assert callerBalanceBefore == callerBalanceAfter;
        assert otherBalanceBefore == otherBalanceAfter;
    }

    /**
    * @notice Prove "participants/bug9.patch"
    * State transition: transfer functions change sender and recipient balances correctly
    **/
    rule transferChangeSenderRecipientBalances(method f, env e, address sender, address recipient) 
        filtered { f -> transferFunctions(f) } {

        setupUser(e, sender);
        setupUser(e, recipient);
        require sender != recipient;

        setupEnv(e);

        uint256 senderBalanceBefore = balanceOf(sender);
        uint256 recipientBalanceBefore = balanceOf(recipient);

        calldataarg arg;
        f(e, arg);

        uint256 senderBalanceAfter = balanceOf(sender);
        uint256 recipientBalanceAfter = balanceOf(recipient);

        assert senderBalanceBefore - senderBalanceAfter > 0 && recipientBalanceAfter - recipientBalanceBefore > 0
            => senderBalanceBefore - senderBalanceAfter == recipientBalanceAfter - recipientBalanceBefore;
    }

    /**
    * @notice Prove "participants/bug10.patch"
    * Hight level: transfer functions don't affect user rewards
    **/
    rule transferDontAffectUserRewards(method f, env e, address anyUser) 
        filtered { f -> transferFunctions(f) } {

        setupUser(e, anyUser);

        setupEnv(e);

        address rewardToken;
        require rewardToken == _DummyERC20_rewardToken;

        mathint claimableRewardsBefore = getClaimableRewards(e, anyUser, rewardToken);
        
        calldataarg arg;
        f(e, arg);

        mathint claimableRewardsAfter = getClaimableRewards(e, anyUser, rewardToken);

        assert claimableRewardsBefore == claimableRewardsAfter;
    }

    /**
    * @notice Prove "participants/bug11.patch"
    * Hight level: transfer functions don't affect users' underlying assets
    **/
    rule transferDontAffectUserUnderlyingAssets(method f, env e, address anyUser) 
        filtered { f -> transferFunctions(f) } {

        setupUser(e, anyUser);

        setupEnv(e);

        uint256 anyUserUnderlyingBalanceBefore = _AToken.balanceOf(e, anyUser);
        
        calldataarg arg;
        f(e, arg);

        uint256 anyUserUnderlyingBalanceAfter = _AToken.balanceOf(e, anyUser);

        assert anyUserUnderlyingBalanceBefore == anyUserUnderlyingBalanceAfter;
    }

    /**
    * @notice Prove "participants/bug12.patch"
    * State transition: `withdraw()` or `redeem()` should burn owner's shares or revert
    **/
    rule withdrawRedeemBurnOwnerShares(method f, env e) 
        filtered { f -> burnFunctions(f) } {
        
        address owner;
        setupUser(e, owner);
        require owner == e.msg.sender;

        address receiver;
        setupUser(e, receiver);
        require owner != receiver;

        setupEnv(e);

        uint256 ownerBalanceBefore = balanceOf(owner);

        address amount;
        uint256 result;
        if(f.selector == withdraw(uint256, address, address).selector) {
            result = withdraw(e, amount, receiver, owner);
        } else { // f.selector == redeem(uint256, address, address).selector
            result = redeem(e, amount, receiver, owner);
        }

        uint256 ownerBalanceAfter = balanceOf(owner);

        assert result != 0 => ownerBalanceBefore != ownerBalanceAfter;
    }

    /**
    * @notice Prove "participants/bug13.patch"
    * State transition: `withdraw()` or `redeem()` should burn only one user's shares 
    **/
    rule burnOnlyOneUserShares(method f, env e) 
        filtered { f -> burnFunctions(f) } {
        
        address owner;
        setupUser(e, owner);
        require owner == e.msg.sender;

        address receiver;
        setupUser(e, receiver);
        require owner != receiver;

        address anyUser;
        setupUser(e, anyUser);
        require anyUser != owner;

        setupEnv(e);

        uint256 anyUserBefore = balanceOf(anyUser);

        address amount;
        uint256 result;
        if(f.selector == withdraw(uint256, address, address).selector) {
            result = withdraw(e, amount, receiver, owner);
        } else { // f.selector == redeem(uint256, address, address).selector
            result = redeem(e, amount, receiver, owner);
        }

        uint256 anyUserAfter = balanceOf(anyUser);

        assert anyUserBefore == anyUserAfter;
    }
