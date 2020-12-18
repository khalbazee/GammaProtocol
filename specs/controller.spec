using DummyERC20C as collateralToken
using MarginPool as pool
using Whitelist as whitelist
using OtokenHarnessA as shortOtoken
using OtokenHarnessB as longOtoken

methods {
    //The tracked asset balance of the system
    pool.getStoredBalance(address) returns uint256 envfree
    
    // ERC20 functions
    collateralToken.totalSupply() returns uint256 envfree
    shortOtoken.totalSupply() returns uint256 envfree
    collateralToken.balanceOf(address) returns uint256 envfree
    longOtoken.balanceOf(address) returns uint256 envfree
    shortOtoken.balanceOf(address) returns uint256 envfree

    // get the cash value for an otoken afte rexpiry
    getPayout(address, uint256) returns uint256 envfree
    // get the amount of collateral that can be taken out of a vault
    getProceed(address, uint256) returns uint256 envfree

    //the amount of collateral in an index in a vault of an owner. i.e.,  vaults[owner][index].collateralAmounts[i]
    getVaultCollateralAmount(address, uint256, uint256)  returns uint256 envfree
    //the collateral asset of an index in a vault of an owner. i.e., vaults[owner][index].collateralAssets(i)
    getVaultCollateralAsset(address, uint256, uint256)  returns address envfree
    //the amount of long in an index in a vault of an owner. i.e.,  vaults[owner][index].longAmounts[i]
    getVaultLongAmount(address, uint256, uint256)  returns uint256 envfree
    //the long oToken in an index in a vault of an owner. i.e.,  vaults[owner][index].longOtoken[i]
    getVaultLongOtoken(address, uint256, uint256)  returns address envfree
    //the amount of long in an index in a vault of an owner. i.e.,  vaults[owner][index].shortAmounts[i]
    getVaultShortAmount(address, uint256, uint256)  returns uint256 envfree
    //the long oToken in an index in a vault of an owner. i.e.,  vaults[owner][index].shortOtoken[i]
    getVaultShortOtoken(address, uint256, uint256)  returns address envfree
	// checks if the vault is expired (true when there is an otoken which we can check expiry for)
    isVaultExpired(address, uint256) returns bool
    // checks if vault is "small" all lengths shorter than a constant
    smallVault(address, uint256, uint256) returns bool envfree
    // checks that a vault is valid
    isValidVault(address, uint256) returns bool envfree

    // The total supply of an asset. i.e., asset.totalSupply()
    assetTotalSupply(address) returns uint256 envfree
    whitelist.isWhitelistedOtoken(address) returns bool envfree
    whitelist.isWhitelistedCollateral(address) returns bool envfree
}

summaries {
    expiryTimestamp() => CONSTANT;
    burnOtoken(address, uint256) => CONSTANT;

}

rule settleVault(address owner, uint256 vaultId, uint256 index, address oToken, address to, address collateral) {
    env e;
    require oToken == shortOtoken;
    require collateral == collateralToken;
    require isValidVault(owner, vaultId); 
    require getVaultShortOtoken(owner, vaultId, index) == oToken;
    require getVaultCollateralAsset(owner, vaultId, index) == collateral;
    uint256 collateralVaultBefore = getProceed(owner, vaultId);
    // uint256 supplyBefore = shortOtoken.totalSupply();
    // uint256 collateralBalanceBefore = collateralToken.balanceOf(pool);

    sinvoke settleVault(e, owner, vaultId, to);

    // uint256 shortVaultAfter = getVaultShortAmount(owner, vaultId, index);
    // uint256 supplyAfter = shortOtoken.totalSupply();
    // uint256 collateralBalanceAfter = collateralToken.balanceOf(pool);
    uint256 collateralVaultAfter = getProceed(owner, vaultId);

    // assert shortVaultAfter == 0;
    assert collateralVaultAfter == 0; 
    // assert supplyAfter == supplyBefore;
    // assert collateralBalanceBefore - collateralBalanceAfter == collateralVaultBefore;

}

rule collateralWithdrawsRestricted(address owner, uint256 vaultId, uint256 index, method f) {
    env e;
    uint256 collateralBalanceBefore = collateralToken.balanceOf(pool);
    calldataarg arg;
    sinvoke f(e, arg);
    uint256 collateralBalanceAfter = collateralToken.balanceOf(pool);

    assert collateralBalanceAfter < collateralBalanceBefore => (f.selector == settleVault(address,uint256,address).selector) 
                                                            || (f.selector == redeemB(address,uint256).selector)
                                                            || (f.selector == redeemA(address,uint256).selector)
                                                            || (f.selector == withdrawCollateral(address,uint256,address,uint256,uint256).selector);
}

rule optionWithdrawsRestricted(address owner, uint256 vaultId, uint256 index, method f) {
    env e;
    uint256 otokenBalanceBefore = shortOtoken.balanceOf(pool);
    calldataarg arg;
    sinvoke f(e, arg);
    uint256 otokenBalanceAfter = shortOtoken.balanceOf(pool);

    assert otokenBalanceAfter < otokenBalanceBefore => (f.selector == withdrawLongA(address, uint256, address, uint256, uint256).selector);
}