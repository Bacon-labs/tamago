import Contracts.Common
import Compiler.ECM
import Tamago.Common.Events

namespace Tamago.Tokens

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Compiler.Yul

def erc4626AssetSafeTransferFromEvent
    (token fromAddr toAddr : Address) (amount : Uint256) : Event :=
  {
    name := "ERC4626AssetSafeTransferFrom",
    args := [addressToWord token, addressToWord fromAddr, addressToWord toAddr, amount],
    indexedArgs := []
  }

def erc4626AssetSafeTransferEvent
    (token fromAddr toAddr : Address) (amount : Uint256) : Event :=
  {
    name := "ERC4626AssetSafeTransfer",
    args := [addressToWord token, addressToWord fromAddr, addressToWord toAddr, amount],
    indexedArgs := []
  }

def traceERC4626AssetSafeTransferFrom
    (token fromAddr toAddr : Address) (amount : Uint256) : Contract Unit :=
  fun state =>
    ContractResult.success () { state with
      events := state.events ++ [erc4626AssetSafeTransferFromEvent token fromAddr toAddr amount]
    }

def traceERC4626AssetSafeTransfer
    (token toAddr : Address) (amount : Uint256) : Contract Unit :=
  fun state =>
    ContractResult.success () { state with
      events :=
        state.events ++
          [erc4626AssetSafeTransferEvent token state.thisAddress toAddr amount]
    }

def safeTransferFrom
    (token fromAddr toAddr : Address) (amount : Uint256) : Contract Unit := do
  Contracts.safeTransferFrom token fromAddr toAddr amount
  traceERC4626AssetSafeTransferFrom token fromAddr toAddr amount

def safeTransfer (token toAddr : Address) (amount : Uint256) : Contract Unit := do
  Contracts.safeTransfer token toAddr amount
  traceERC4626AssetSafeTransfer token toAddr amount

namespace ERC4626Runtime

def selfAddress (_unused : Uint256) : Contract Address :=
  Verity.contractAddress

def selfAddressModule : Compiler.ECM.ExternalCallModule where
  name := "selfAddress"
  numArgs := 0
  resultVars := ["self"]
  writesState := false
  readsState := true
  axioms := ["self_address_interface"]
  compile := fun _ctx args => do
    match args with
    | [] => pure [YulStmt.let_ "self" (YulExpr.call "address" [])]
    | _ => throw "selfAddress expects no arguments"

def selfAddress_model : Compiler.CompilationModel.FunctionSpec := {
  name := "selfAddress"
  params := [
    { name := "unused", ty := Compiler.CompilationModel.ParamType.uint256 }
  ]
  returnType := some Compiler.CompilationModel.FieldType.address
  returns := [Compiler.CompilationModel.ParamType.address]
  body := [
    Compiler.CompilationModel.Stmt.ecm selfAddressModule [],
    Compiler.CompilationModel.Stmt.return
      (Compiler.CompilationModel.Expr.localVar "self")
  ]
}

end ERC4626Runtime

/-
@title ERC4626
@notice Tokenized vault with ERC20-style share accounting, asset/share previews,
deposits, minting, withdrawals, and redemptions.
@dev The underlying asset token is immutable after deployment. The vault tracks
managed assets explicitly and uses safe ERC20 transfers for underlying asset
movement. Share math uses virtual assets and shares to avoid empty-vault
division edge cases.
Limitations: ERC20 metadata accessors `name()` and `symbol()` are intentionally
not implemented.
-/
verity_contract ERC4626Base where
  storage
    tokenSupply : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
    allowances : Address → Address → Uint256 := slot 3
    managedAssets : Uint256 := slot 4

  constants
    maxUint256 : Uint256 := (sub 0 1)

  immutables
    assetToken : Address := underlyingAsset

  /-
  @notice Initializes the vault with an underlying asset and zero share supply.
  @param underlyingAsset ERC20 asset token managed by the vault.
  -/
  constructor (underlyingAsset : Address) := do
    require (underlyingAsset != zeroAddress) "Invalid asset"
    setStorage tokenSupply 0
    setStorage managedAssets 0

  /-
  @notice Returns the share token decimal precision.
  @return Fixed decimal precision of 18.
  -/
  function view decimals () : Uint256 := do
    return 18

  /-
  @notice Returns the total share supply.
  @return Current total share supply.
  -/
  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage tokenSupply
    return currentSupply

  /-
  @notice Returns an account's share balance.
  @param account Address whose share balance is queried.
  @return Current share balance for `account`.
  -/
  function view balanceOf (account : Address) : Uint256 := do
    let currentBalance ← getMapping balances account
    return currentBalance

  /-
  @notice Returns the share allowance from an owner to a spender.
  @param ownerAddr Share owner address.
  @param spender Address allowed to spend from `ownerAddr`.
  @return Remaining share allowance.
  -/
  function view allowance (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowances ownerAddr spender
    return currentAllowance

  /-
  @notice Sets the caller's share allowance for a spender.
  @param spender Address allowed to spend the caller's shares.
  @param amount Share allowance amount to set.
  @return True on success.
  -/
  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount
    emit "Approval" [addressToWord sender, addressToWord spender, amount]
    return true

  /-
  @notice Transfers shares from the caller to another address.
  @param toAddr Recipient address.
  @param amount Share amount to transfer.
  @return True on success.
  -/
  function transfer (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let senderBalance ← getMapping balances sender
    require (senderBalance >= amount) "Insufficient balance"
    if sender == toAddr then
      pure ()
    else
      let recipientBalance ← getMapping balances toAddr
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balances sender (sub senderBalance amount)
      setMapping balances toAddr newRecipientBalance
    emit "Transfer" [addressToWord sender, addressToWord toAddr, amount]
    return true

  /-
  @notice Transfers shares from an approved owner to another address.
  @param fromAddr Address whose shares are debited.
  @param toAddr Recipient address.
  @param amount Share amount to transfer.
  @return True on success.
  -/
  function transferFrom (fromAddr : Address, toAddr : Address, amount : Uint256) : Bool := do
    let spender ← msgSender
    let currentAllowance ← getMapping2 allowances fromAddr spender
    require (currentAllowance >= amount) "Insufficient allowance"
    let fromBalance ← getMapping balances fromAddr
    require (fromBalance >= amount) "Insufficient balance"

    if fromAddr == toAddr then
      pure ()
    else
      let toBalance ← getMapping balances toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "Recipient balance overflow"
      setMapping balances fromAddr (sub fromBalance amount)
      setMapping balances toAddr newToBalance

    if currentAllowance == maxUint256 then
      pure ()
    else
      setMapping2 allowances fromAddr spender (sub currentAllowance amount)
    emit "Transfer" [addressToWord fromAddr, addressToWord toAddr, amount]
    return true

  /-
  @notice Returns the underlying asset token.
  @return Asset token address.
  -/
  function view asset () : Address := do
    return assetToken

  /-
  @notice Returns total managed assets.
  @return Current managed asset amount.
  -/
  function view totalAssets () : Uint256 := do
    let currentAssets ← getStorage managedAssets
    return currentAssets

  /-
  @notice Converts an asset amount to shares using current vault accounting.
  @param assets Asset amount to convert.
  @return Equivalent share amount rounded down.
  -/
  function view convertToShares (assets : Uint256) : Uint256 := do
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let product := mul assets (add currentSupply 1)
    return div product (add currentAssets 1)

  /-
  @notice Converts a share amount to assets using current vault accounting.
  @param shares Share amount to convert.
  @return Equivalent asset amount rounded down.
  -/
  function view convertToAssets (shares : Uint256) : Uint256 := do
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let product := mul shares (add currentAssets 1)
    return div product (add currentSupply 1)

  /-
  @notice Returns the maximum assets that can be deposited for a receiver.
  @param _receiver Receiver address, unused by this implementation.
  @return Maximum uint256.
  -/
  function view maxDeposit (_receiver : Address) : Uint256 := do
    return maxUint256

  /-
  @notice Returns the maximum shares that can be minted for a receiver.
  @param _receiver Receiver address, unused by this implementation.
  @return Maximum uint256.
  -/
  function view maxMint (_receiver : Address) : Uint256 := do
    return maxUint256

  /-
  @notice Returns the maximum assets an owner can withdraw.
  @param ownerAddr Share owner address.
  @return Withdrawable asset amount.
  -/
  function view maxWithdraw (ownerAddr : Address) : Uint256 := do
    let ownerShares ← getMapping balances ownerAddr
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let product := mul ownerShares (add currentAssets 1)
    return div product (add currentSupply 1)

  /-
  @notice Returns the maximum shares an owner can redeem.
  @param ownerAddr Share owner address.
  @return Redeemable share amount.
  -/
  function view maxRedeem (ownerAddr : Address) : Uint256 := do
    let ownerShares ← getMapping balances ownerAddr
    return ownerShares

  /-
  @notice Previews shares minted by an asset deposit.
  @param assets Asset amount to deposit.
  @return Share amount minted, rounded down.
  -/
  function view previewDeposit (assets : Uint256) : Uint256 := do
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let product := mul assets (add currentSupply 1)
    return div product (add currentAssets 1)

  /-
  @notice Previews assets required to mint shares.
  @param shares Share amount to mint.
  @return Asset amount required, rounded up.
  -/
  function view previewMint (shares : Uint256) : Uint256 := do
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let denominator := add currentSupply 1
    let product := mul shares (add currentAssets 1)
    let rounded := add product (sub denominator 1)
    return div rounded denominator

  /-
  @notice Previews shares burned by an asset withdrawal.
  @param assets Asset amount to withdraw.
  @return Share amount burned, rounded up.
  -/
  function view previewWithdraw (assets : Uint256) : Uint256 := do
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let denominator := add currentAssets 1
    let product := mul assets (add currentSupply 1)
    let rounded := add product (sub denominator 1)
    return div rounded denominator

  /-
  @notice Previews assets returned by redeeming shares.
  @param shares Share amount to redeem.
  @return Asset amount returned, rounded down.
  -/
  function view previewRedeem (shares : Uint256) : Uint256 := do
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let product := mul shares (add currentAssets 1)
    return div product (add currentSupply 1)

  /-
  @notice Deposits assets and mints vault shares to a receiver.
  @param assets Asset amount to pull from the caller.
  @param receiver Address that receives minted shares.
  @return Share amount minted.
  -/
  function allow_post_interaction_writes deposit (assets : Uint256, receiver : Address) : Uint256 := do
    let sender ← msgSender
    let currentAsset := assetToken
    let self ← ERC4626Runtime.selfAddress 0
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let shares := div (mul assets (add currentSupply 1)) (add currentAssets 1)
    let receiverBalance ← getMapping balances receiver
    let newReceiverBalance ← requireSomeUint (safeAdd receiverBalance shares) "Balance overflow"
    let newSupply ← requireSomeUint (safeAdd currentSupply shares) "Supply overflow"
    let newManagedAssets ← requireSomeUint (safeAdd currentAssets assets) "Total assets overflow"
    emit "Transfer" [addressToWord zeroAddress, addressToWord receiver, shares]
    emit "Deposit" [addressToWord sender, addressToWord receiver, assets, shares]
    safeTransferFrom currentAsset sender self assets
    setMapping balances receiver newReceiverBalance
    setStorage tokenSupply newSupply
    setStorage managedAssets newManagedAssets
    return shares

  /-
  @notice Mints an exact share amount to a receiver by pulling assets.
  @param shares Share amount to mint.
  @param receiver Address that receives minted shares.
  @return Asset amount pulled from the caller.
  -/
  function allow_post_interaction_writes mint (shares : Uint256, receiver : Address) : Uint256 := do
    let sender ← msgSender
    let currentAsset := assetToken
    let self ← ERC4626Runtime.selfAddress 0
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let denominator := add currentSupply 1
    let product := mul shares (add currentAssets 1)
    let assets := div (add product (sub denominator 1)) denominator
    let receiverBalance ← getMapping balances receiver
    let newReceiverBalance ← requireSomeUint (safeAdd receiverBalance shares) "Balance overflow"
    let newSupply ← requireSomeUint (safeAdd currentSupply shares) "Supply overflow"
    let newManagedAssets ← requireSomeUint (safeAdd currentAssets assets) "Total assets overflow"
    emit "Transfer" [addressToWord zeroAddress, addressToWord receiver, shares]
    emit "Deposit" [addressToWord sender, addressToWord receiver, assets, shares]
    safeTransferFrom currentAsset sender self assets
    setMapping balances receiver newReceiverBalance
    setStorage tokenSupply newSupply
    setStorage managedAssets newManagedAssets
    return assets

  /-
  @notice Withdraws an exact asset amount by burning owner shares.
  @param assets Asset amount to withdraw.
  @param receiver Address that receives withdrawn assets.
  @param ownerAddr Share owner whose shares are burned.
  @return Share amount burned.
  -/
  function withdraw (assets : Uint256, receiver : Address, ownerAddr : Address) : Uint256 := do
    let sender ← msgSender
    let currentAsset := assetToken
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let denominator := add currentAssets 1
    let product := mul assets (add currentSupply 1)
    let shares := div (add product (sub denominator 1)) denominator
    let ownerBalance ← getMapping balances ownerAddr
    let maxAssets := div (mul ownerBalance (add currentAssets 1)) (add currentSupply 1)
    require (assets <= maxAssets) "Withdraw more than max"
    let currentAllowance ← getMapping2 allowances ownerAddr sender

    if sender == ownerAddr then
      pure ()
    else
      require (currentAllowance >= shares) "Insufficient allowance"

    require (ownerBalance >= shares) "Insufficient balance"
    require (currentSupply >= shares) "Insufficient supply"
    require (currentAssets >= assets) "Insufficient assets"
    if (sender != ownerAddr) && (currentAllowance != maxUint256) then
      setMapping2 allowances ownerAddr sender (sub currentAllowance shares)
    else
      pure ()
    setMapping balances ownerAddr (sub ownerBalance shares)
    setStorage tokenSupply (sub currentSupply shares)
    setStorage managedAssets (sub currentAssets assets)
    emit "Transfer" [addressToWord ownerAddr, addressToWord zeroAddress, shares]
    emit "Withdraw" [addressToWord sender, addressToWord receiver, addressToWord ownerAddr, assets, shares]
    safeTransfer currentAsset receiver assets
    return shares

  /-
  @notice Redeems an exact share amount for assets.
  @param shares Share amount to redeem.
  @param receiver Address that receives withdrawn assets.
  @param ownerAddr Share owner whose shares are burned.
  @return Asset amount returned.
  -/
  function redeem (shares : Uint256, receiver : Address, ownerAddr : Address) : Uint256 := do
    let sender ← msgSender
    let currentAsset := assetToken
    let currentAssets ← getStorage managedAssets
    let currentSupply ← getStorage tokenSupply
    let ownerBalance ← getMapping balances ownerAddr
    require (shares <= ownerBalance) "Redeem more than max"
    let assets := div (mul shares (add currentAssets 1)) (add currentSupply 1)
    let currentAllowance ← getMapping2 allowances ownerAddr sender

    if sender == ownerAddr then
      pure ()
    else
      require (currentAllowance >= shares) "Insufficient allowance"

    require (currentSupply >= shares) "Insufficient supply"
    require (currentAssets >= assets) "Insufficient assets"
    if (sender != ownerAddr) && (currentAllowance != maxUint256) then
      setMapping2 allowances ownerAddr sender (sub currentAllowance shares)
    else
      pure ()
    setMapping balances ownerAddr (sub ownerBalance shares)
    setStorage tokenSupply (sub currentSupply shares)
    setStorage managedAssets (sub currentAssets assets)
    emit "Transfer" [addressToWord ownerAddr, addressToWord zeroAddress, shares]
    emit "Withdraw" [addressToWord sender, addressToWord receiver, addressToWord ownerAddr, assets, shares]
    safeTransfer currentAsset receiver assets
    return assets

namespace ERC4626

abbrev assetToken := ERC4626Base.__verity_immutable_slot_assetToken
abbrev tokenSupply := ERC4626Base.tokenSupply
abbrev balances := ERC4626Base.balances
abbrev allowances := ERC4626Base.allowances
abbrev managedAssets := ERC4626Base.managedAssets
abbrev maxUint256 := ERC4626Base.maxUint256

abbrev decimals := ERC4626Base.decimals
abbrev totalSupply := ERC4626Base.totalSupply
abbrev balanceOf := ERC4626Base.balanceOf
abbrev allowance := ERC4626Base.allowance
abbrev approve := ERC4626Base.approve
abbrev transfer := ERC4626Base.transfer
abbrev transferFrom := ERC4626Base.transferFrom
abbrev asset := ERC4626Base.asset
abbrev totalAssets := ERC4626Base.totalAssets
abbrev convertToShares := ERC4626Base.convertToShares
abbrev convertToAssets := ERC4626Base.convertToAssets
abbrev maxDeposit := ERC4626Base.maxDeposit
abbrev maxMint := ERC4626Base.maxMint
abbrev maxWithdraw := ERC4626Base.maxWithdraw
abbrev maxRedeem := ERC4626Base.maxRedeem
abbrev previewDeposit := ERC4626Base.previewDeposit
abbrev previewMint := ERC4626Base.previewMint
abbrev previewWithdraw := ERC4626Base.previewWithdraw
abbrev previewRedeem := ERC4626Base.previewRedeem
abbrev deposit := ERC4626Base.deposit
abbrev mint := ERC4626Base.mint
abbrev withdraw := ERC4626Base.withdraw
abbrev redeem := ERC4626Base.redeem

def spec : Compiler.CompilationModel.CompilationModel :=
  { ERC4626Base.spec with
    name := "ERC4626"
    events := [
      Tamago.Common.Events.transfer,
      Tamago.Common.Events.approval,
      Tamago.Common.Events.deposit,
      Tamago.Common.Events.withdraw
    ] }

end ERC4626

end Tamago.Tokens
