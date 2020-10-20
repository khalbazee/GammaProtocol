using anOtokenA as oTokenA
using MarginPoolHarness as pool


methods {
    //The tracked asset balance of the system
    pool.getStoredBalance(address) returns uint256 envfree
    //The asset balance of MarginPool. i.e.,  asset.balanceOf(MarginPool)
    assetBalanceOfPool(address) returns uint256 envfree
    // the total supply of an asset. i.e., asset.totalSupply()
    assetTotalSupply(address) returns uint256 envfree
    //the amount of collateral in an index in a vault of an owner. i.e.,  vaults[owner][index].collateralAmounts[i]
    getVaultCollateralAmount(address, uint256, uint256)  returns uint256 envfree
    //the collateral asset of an index in a vault of an owner. i.e., vaults[owner][index].collateralAssets(i)
    getVaultCollateralAsset(address, uint256, uint256)  returns address envfree
    //the amount of long in an index in a vault of an owner. i.e.,  vaults[owner][index].longAmounts[i]
    getVaultLongAmount(address, uint256, uint256)  returns address envfree
    //the long oToken in an index in a vault of an owner. i.e.,  vaults[owner][index].longOtoken[i]
    getVaultLongOtoken(address, uint256, uint256)  returns uint256 envfree
    //the amount of long in an index in a vault of an owner. i.e.,  vaults[owner][index].shortAmounts[i]
    getVaultShortAmount(address, uint256, uint256)  returns address envfree
    //the long oToken in an index in a vault of an owner. i.e.,  vaults[owner][index].shortOtoken[i]
    getVaultShortOtoken(address, uint256, uint256)  returns uint256 envfree

    //Is first address authorized the second one to manipulate his vaults
    isAuthorized(address, address) returns bool envfree

    owner() returns address envfree
    anOtokenA() returns address envfree
    anOtokenB() returns address envfree
    dummyERC20C() returns address envfree
    isValidAsset(address) returns bool envfree

}
/***
In formal verification we typically bound the number of instance
We use two oTokens:
OtokenA
OtokenB
and three erc20 tokens:
DummyERC20A
DummyERC20B
DummyERC20B
We use the following connections:
OtokenA.underlyingAsset=OtokenB.underlyingAsset=DummyERC20A
OtokenA.strikeAsset=OtokenB.strikeAsset=DummyERC20B
OtokenA.collateralAsset=OtokenB.collateralAsset=DummyERC20C
****/

/*
rule onlyOwnerCanAffectAbilityToRun(method f, method g) {
    address controllerOwner = owner();

    storage init_storage = lastStorage;
    // f, and g;f succeed all the same
    env e;
    calldataarg arg;
    sinvoke f(e, arg);

    env e2;
    calldataarg arg2;
    sinvoke g(e2, arg2) at init_storage;
    invoke f(e, arg);
    bool fAfterGSucceeded = !lastReverted;

    assert e2.msg.sender != controllerOwner => fAfterGSucceeded;
    // Expecting violations on pauser and terminator
}
*/

/**
@title Valid balance of the system
@notice The balance of the system at an external asset is correlated with the tracked  asset balance
        getStoredBalance(asset) ג‰₪ asset.balanceOf(MarginPool)
*/
invariant validBalanceOfTheSystem(address asset)
        isValidAsset(asset) =>  (pool.getStoredBalance(asset) <= assetBalanceOfPool(asset) )

/**
@title Valid balance with respect to total collateral
@notice The sum of a collateral asset across vaults matches the assetBalance stored in the margin pool
        Vasset = { (v,i) v גˆˆ Vaults.  v.collateralAssets(i) = asset }
        getStoredBalance(asset) = גˆ‘(v,i) גˆˆ Vasset. v.collateralAmounts[i]

This is proven by showing that change to a single vault is coherent with the change to the stored balance

*/
rule validBalanceTotalCollateral(address owner, uint256 vaultId, uint256 index, address asset, method f)
description "$f breaks the validity of stored balance of collateral asset"
{
    env e;
    calldataarg arg;
    require getVaultCollateralAsset(owner, vaultId, index) == asset;
    require asset == dummyERC20C();
    uint256 collateralVaultBefore = getVaultCollateralAmount(owner, vaultId, index);
    uint256 poolBalanceBefore = pool.getStoredBalance(asset);
    sinvoke f(e, arg);
    uint256 collateralVaultAfter = getVaultCollateralAmount(owner, vaultId, index);
    uint256 poolBalanceAfter = pool.getStoredBalance(asset);
    assert collateralVaultBefore != collateralVaultAfter => ( poolBalanceAfter - poolBalanceBefore ==  collateralVaultAfter - collateralVaultBefore);
}

/**
@title Valid balance of long oTokens
@notice The sum of a long asset across vaults matches the assetBalance stored in the margin pool
        Vasset = { (v,i) v גˆˆ Vaults.  v.longOtokens(i) = oToken}
        getStoredBalance(oToken) = גˆ‘(v,i) גˆˆ Vasset. v.longAmounts[i]
*/
rule validBalanceTotalLong(address owner, uint256 vaultId, uint256 index, address oToken, method f)
description "$f breaks the validity of stored balance of long asset"
{
    env e;
    calldataarg arg;
    require getVaultLongOtoken(owner, vaultId, index) == oToken;
    require oToken == dummyERC20C();
    uint256 longVaultBefore = getVaultLongAmount(owner, vaultId, index);
    uint256 poolBalanceBefore = pool.getStoredBalance(oToken);
    sinvoke f(e, arg);
    uint256 longVaultAfter = getVaultLongAmount(owner, vaultId, index);
    uint256 poolBalanceAfter = pool.getStoredBalance(oToken);
    assert longVaultBefore != longVaultAfter => ( poolBalanceAfter - poolBalanceBefore ==  longVaultAfter - longVaultBefore);
}

/**
@title Valid supply of short oToken
@notice The sum of a short asset across vaults matches the supply of that short oToken
        Vasset = { (v,i) v גˆˆ Vaults.  v.shortOtokens(i) = oToken}
        oToken.totalSupply() = גˆ‘(v,i) גˆˆ Vasset. v.shortAmounts[i]
*/
rule validBalanceTotalShort(address owner, uint256 vaultId, uint256 index, address oToken, method f)
description "$f breaks the validity of stored balance of short asset"
{
    env e;
    calldataarg arg;
    require getVaultShortOtoken(owner, vaultId, index) == oToken;
    require oToken == dummyERC20C();
    uint256 shortVaultBefore = getVaultShortAmount(owner, vaultId, index);
    uint256 longVaultBefore = getVaultLongAmount(owner, vaultId, index);

    uint256 supplyBefore = assetTotalSupply(oToken);
    sinvoke f(e, arg);
    uint256 shortVaultAfter = getVaultShortAmount(owner, vaultId, index);
    uint256 supplyAfter = assetTotalSupply(oToken);
    assert shortVaultBefore != shortVaultAfter => ( supplyAfter - supplyBefore ==  shortVaultAfter - shortVaultBefore);
}


/**
@title No effect on another vault
@notice Operation can affect at most one vault (of the same or other user)
        { v1= vault(a,i) ג‹€ v2= vault(b,j) ג‹€ ( a ג‰  b ג‹ i ג‰  j ) }
            Op
        { vault(a,i) = v1 ג‹ vault(a,i) = v2 }

*/
//A stronge property: change to one idex of a single vault.
//should hols on all function except settleVault
rule changeToOneVaultOneIndex(address owner1, address owner2, uint256 vaultId1, uint256 vaultId2, uint256 index1, uint256 index2, method f)
description "$f can change more than one vault one index"
{
    env e;
    calldataarg arg;
    require vaultId1!=vaultId2 || index1!=index2 || owner1!=owner2;
    //vault 1 data
    uint256 shortAmount1 = getVaultShortAmount(owner1, vaultId1, index1);
    uint256 longAmount1 = getVaultLongAmount(owner1, vaultId1, index1);
    uint256 oTokenShort1 = getVaultShortOtoken(owner1, vaultId1, index1);
    uint256 oTokenLong1 = getVaultLongOtoken(owner1, vaultId1, index1);
    address collateralAsset1 = getVaultCollateralAsset(owner1, vaultId1, index1);
    uint256 collateralVault1 = getVaultCollateralAmount(owner1, vaultId1, index1);
    //vault 2 data
    uint256 shortAmount2 = getVaultShortAmount(owner2, vaultId2, index2);
    uint256 longAmount2 = getVaultLongAmount(owner2, vaultId2, index2);
    uint256 oTokenShort2 = getVaultShortOtoken(owner2, vaultId2, index2);
    uint256 oTokenLong2 = getVaultLongOtoken(owner2, vaultId2, index2);
    address collateralAsset2 = getVaultCollateralAsset(owner2, vaultId2, index2);
    uint256 collateralVault2 = getVaultCollateralAmount(owner2, vaultId2, index2);
    require f.selector != settleVault(address,uint256,address).selector;
    sinvoke f(e, arg);
    assert( (   shortAmount1 == getVaultShortAmount(owner1, vaultId1, index1) &&
                longAmount1 == getVaultLongAmount(owner1, vaultId1, index1) &&
                oTokenShort1 == getVaultShortOtoken(owner1, vaultId1, index1) &&
                oTokenLong1 == getVaultLongOtoken(owner1, vaultId1, index1) &&
                collateralAsset1 == getVaultCollateralAsset(owner1, vaultId1, index1) &&
                collateralVault1 == getVaultCollateralAmount(owner1, vaultId1, index1) ) ||
              ( shortAmount2 == getVaultShortAmount(owner2, vaultId2, index2) &&
                longAmount2 == getVaultLongAmount(owner2, vaultId2, index2) &&
                oTokenShort2 == getVaultShortOtoken(owner2, vaultId2, index2) &&
                oTokenLong2 == getVaultLongOtoken(owner2, vaultId2, index2) &&
                collateralAsset2 == getVaultCollateralAsset(owner2, vaultId2, index2) &&
                collateralVault2 == getVaultCollateralAmount(owner2, vaultId2, index2) ) );
}

rule noChangeToOtherVaultValue(address owner, address otherOwner, uint256 vaultId, uint256 otherVaultId, method f)
description "$f can change other's vault"
{
    env e;
    calldataarg arg;
    require vaultId != otherVaultId || owner != otherOwner;
    require e.msg.sender == owner &&  !isAuthorized(owner,otherOwner);
    uint256 valueVault = getProceed(e, otherOwner, otherVaultId);
    sinvoke f(e, arg);
    assert( getProceed(e, otherOwner, otherVaultId) == valueVault );
}

//rule userCanNotGainMoney(address owner, uint256 vaultId, address asset, uint256 index,


rule inverseDepositLongWithdrawLong(address owner, uint256 vaultId, address from, uint256 index, uint256 amount) {
    env e;
    uint256 vaultBalanceBefore = getProceed(e, owner, vaultId);
    address oTokenA = anOtokenA();
    uint256 poolOtokenBalanceBefore = pool.getStoredBalance(oTokenA);
    require (index == 0 ); //due to an issue in MarginVault, remove once the issue is fixed
    sinvoke depositLongA(e, owner, vaultId, from, index, amount); //deposits anOtokenA
    invoke withdrawLongA(e, owner, vaultId, from, index, amount); //withdraws anOtokenA
    assert !lastReverted &&  getProceed(e, owner, vaultId) == vaultBalanceBefore && pool.getStoredBalance(oTokenA) ==  poolOtokenBalanceBefore;
}


rule sanity(method f) {
    env e;
    calldataarg arg;
    sinvoke f(e, arg);
    assert false;

}



