/**
 *
 * TEST ENGINE PARAMETERS
 *
 */

enum actionType {
  OpenVault,
  DepositLongOption,
  WithdrawLongOption,
  DepositCollateral,
  WithdrawCollateral,
  MintShortOption,
  BurnShortOption,
  Redeem,
  SettleVault,
  Call,
}

enum actionRule {
  OpenVault,
  DepositLongOption,
  WithdrawLongOption,
  DepositCollateral,
  WithdrawCollateral,
  MintShortOption,
  BurnShortOption,
  Redeem,
  SettleVault,
  Call,
}

enum vaultIdRule {
  newVault,
  existentVault,
}

export interface Action {
  shortAmount: number
  longAmount: number
  shortStrike: number
  longStrike: number
  collateral: number
  netValue: number
  isExcess: boolean
  oraclePrice: number
}

export interface Actions {
  action: Action[]
}
