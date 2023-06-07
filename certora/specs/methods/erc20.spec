// erc20 methods
methods {
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (uint8)  => DISPATCHER(true) // Fixed to `uint8`
    totalSupply()                         returns (uint256) envfree => DISPATCHER(true)
    balanceOf(address)                    returns (uint256) envfree => DISPATCHER(true)
    allowance(address,address)            returns (uint256) => DISPATCHER(true)
    approve(address,uint256)              returns (bool)    => DISPATCHER(true)
    transfer(address,uint256)             returns (bool)    => DISPATCHER(true)
    // transferFrom(address,address,uint256) returns (bool)    => DISPATCHER(true)
}
