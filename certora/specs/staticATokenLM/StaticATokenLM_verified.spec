import "StaticATokenLM_base.spec"

/////////////////// METHODS ////////////////////////

    methods
    {   
        getReserveData_isActive() returns (bool) envfree
        getReserveData_isPaused() returns (bool) envfree
        getReserveData_isFrozen() returns (bool) envfree

        getClaimableRewards(address, address) returns (uint256)
        saveCastToUint128(uint256) returns (uint128) envfree

        mint(uint256, address) returns (uint256) => DISPATCHER(true)
        deposit(uint256, address, uint16, bool) returns (uint256) => DISPATCHER(true)
        deposit(uint256, address) returns (uint256) => DISPATCHER(true)

        convertToShares(uint256) returns (uint256)
        convertToAssets(uint256) returns (uint256)
        maxRedeemUnderlying(address) returns (uint256)
        maxDepositUnderlying(address) returns (uint256)
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
    
    /// @notice `metaDeposit()` is excluded because of the off-chain cryptography
    definition mintDepositFunctions(method f) returns bool = (
        f.selector == deposit(uint256, address, uint16, bool).selector 
        || f.selector == deposit(uint256, address).selector
        || f.selector == mint(uint256, address).selector
        );
    
////////////////// FUNCTIONS //////////////////////

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
    * @dev Variable Transition: check if `unclaimedRewards` is updated correctly 
    **/
    rule updateUserUnclaimedRewards(env e, address user1, address user2) {
        setupUser(e, user1);
        setupUser(e, user2);
        require e.msg.sender == user1;
        require user1 != user2;

        setupEnv(e);
        address rewardToken;
        require rewardToken == _DummyERC20_rewardToken;

        // Updating of `unclaimedRewards` requires user's balance > 0
        require balanceOf(user1) != 0;
        require balanceOf(user2) != 0;

        // Precalculate `_getClaimableRewards()` call in `_updateUser()`
        mathint claimableRewards1 = saveCastToUint128(getClaimableRewards(e, user1, rewardToken));
        mathint claimableRewards2 = saveCastToUint128(getClaimableRewards(e, user2, rewardToken));

        // Transfer `amount` from `user1` to `user2` to execute `_beforeTokenTransfer()` 
        uint256 amount;
        transfer(e, user2, amount);

        // `_beforeTokenTransfer()` should change users's `unclaimedRewards` the same way
        mathint unclaimedRewards1 = saveCastToUint128(getUnclaimedRewards(user1, rewardToken));
        assert unclaimedRewards1 == claimableRewards1; 
        mathint unclaimedRewards2 = saveCastToUint128(getUnclaimedRewards(user2, rewardToken));
        assert unclaimedRewards2 == claimableRewards2; 
    }
    
    /**
    * @notice Prove "certora/bug6.patch"
    * @dev High-level: minted `assets` should be calculated based of `shares` 
    **/
    rule mintAssetsBasedOnPreviewMint(env e, address user1, address user2) {
        setupUser(e, user1);
        setupUser(e, user2);
        require e.msg.sender == user1;
        require user1 != user2;

        uint256 shares;
        mathint assets = mint(e, shares, user2);

        // Amount of minted assets should be calculated based of `shares`
        assert assets == previewMint(e, shares);
    }
    
    /**
    * @notice Prove "certora/bug9.patch"
    * @dev Unit test: `maxRedeemUnderlying()` should return up to the available amount 
    **/
    rule maxRedeemUnderlyingResult(env e, address user) {
        setupUser(e, user);
        setupEnv(e);

        // Assume the protocol have `ACTIVE` and not have `PAUSED` flags
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
    * @dev High-level: could not get max underlying value when paused or frozen (for deposit) 
    **/
    rule forbidMaxUnderlyingValueWhenPaused(env e, method f, address user) 
        filtered { f -> maxUnderlyingFunctions(f) } {

        uint256 result;

        setupUser(e, user);

        // `maxRedeemUnderlying()`: the protocol have `PAUSED` flag or not have `ACTIVE` flag 
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
    * @dev Valid state: total supply is the summary of tokens of all users
    **/
    invariant balanceSolvency() totalSupply() == sumAllBalance() filtered { f -> !f.isView } {
        preserved with(env e) {
            require e.msg.sender != currentContract;
        }
    }

    /**
    * @notice Prove "participants/bug3.patch"
    * @dev State transition: each possible operation changes the balance of at most two users
    **/
    rule balanceOfChangeMaxTwoUsers(env e, method f, address user1, address user2, address user3) 
        filtered { f -> !f.isView } {

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

        // At least one user's balanced should not changed
        assert (balance1Before == balance1After 
            || balance2Before == balance2After 
            || balance3Before == balance3After
            );
    }
    
    /**
    * @notice Prove "participants/bug4.patch"
    * @dev Unit-test: could not mint zero tokens
    **/
    rule mintDepositPositiveAmount(env e, method f, address caller) 
        filtered { f -> mintDepositFunctions(f) } {
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
    * @dev High-level: `mint()` increases total supply of shares
    **/
    rule mintSharesIncreaseSharesTotalSupply(env e, address caller, uint256 shares, address recipient) {
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

        // Total shares increasing the the same amount as user's sharess
        assert totalSharesAfter > totalSharesBefore;
        assert totalSharesAfter - totalSharesBefore == sharesBalanceAfter - sharesBalanceBefore;
    }
    