import Contracts.Common
import Tamago.Auth.Ownable
import Tamago.Common.Events

namespace Tamago.Tokens

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
@title ERC20
@notice Fungible token with allowances, owner-controlled minting and burning,
and caller-chosen decimal precision.
@dev This contract implements the core ERC20 balance, allowance, transfer,
approval, mint, and burn flows. It also includes Ownable-style owner management.
The decimal precision is supplied at construction and immutable thereafter, so
deployments can match the precision of integrating ecosystems (e.g. 6 for
USDC-style accounting, 18 for ETH-style).
Limitations: metadata accessors `name()` and `symbol()` are intentionally not
implemented.
-/
verity_contract ERC20Base where
  storage
    contractOwner : Address := slot 0
    tokenSupply : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
    allowances : Address → Address → Uint256 := slot 3

  constants
    maxUint256 : Uint256 := (sub 0 1)

  immutables
    tokenDecimals : Uint256 := initialDecimals

  /-
  @notice Initializes token ownership, zero supply, and decimal precision.
  @param initialOwner Address that receives ownership at deployment.
  @param initialDecimals Token decimal precision, fixed for the lifetime of
  the deployment.
  -/
  constructor (initialOwner : Address, initialDecimals : Uint256) := do
    setStorageAddr contractOwner initialOwner
    setStorage tokenSupply 0

  /-
  @notice Returns the token decimal precision set at construction.
  @return Decimal precision recorded in the contract's immutable storage.
  -/
  function view decimals () : Uint256 := do
    return tokenDecimals

  /-
  @notice Returns the total token supply.
  @return Current total supply.
  -/
  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage tokenSupply
    return currentSupply

  /-
  @notice Returns an account balance.
  @param account Address whose balance is queried.
  @return Current token balance for `account`.
  -/
  function view balanceOf (account : Address) : Uint256 := do
    let currentBalance ← getMapping balances account
    return currentBalance

  /-
  @notice Returns the allowance from an owner to a spender.
  @param ownerAddr Token owner address.
  @param spender Address allowed to spend from `ownerAddr`.
  @return Remaining allowance.
  -/
  function view allowance (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowances ownerAddr spender
    return currentAllowance

  /-
  @notice Returns the current contract owner.
  @return Current owner address.
  -/
  function view owner () : Address := do
    let currentOwner ← getStorageAddr contractOwner
    return currentOwner

  /-
  @notice Transfers ownership to a nonzero address.
  @param newOwner Address that will become the owner.
  @return True on success.
  -/
  function transferOwnership (newOwner : Address) : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    require (newOwner != zeroAddress) "Invalid owner"
    setStorageAddr contractOwner newOwner
    emit "OwnershipTransferred" [addressToWord currentOwner, addressToWord newOwner]
    return true

  /-
  @notice Renounces ownership and leaves the token without an owner.
  @return True on success.
  -/
  function renounceOwnership () : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr contractOwner zeroAddress
    emit "OwnershipTransferred" [addressToWord currentOwner, addressToWord zeroAddress]
    return true

  /-
  @notice Sets the caller's allowance for a spender.
  @param spender Address allowed to spend the caller's tokens.
  @param amount Allowance amount to set.
  @return True on success.
  -/
  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount
    emit "Approval" [addressToWord sender, addressToWord spender, amount]
    return true

  /-
  @notice Transfers tokens from the caller to another address.
  @param toAddr Recipient address.
  @param amount Token amount to transfer.
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
  @notice Transfers tokens from an approved owner to another address.
  @param fromAddr Address tokens are debited from.
  @param toAddr Recipient address.
  @param amount Token amount to transfer.
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
  @notice Mints tokens to an address.
  @param toAddr Address that receives minted tokens.
  @param amount Token amount to mint.
  @return True on success.
  -/
  function mint (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balances toAddr
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage tokenSupply
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balances toAddr newBalance
    setStorage tokenSupply newSupply
    emit "Transfer" [addressToWord zeroAddress, addressToWord toAddr, amount]
    return true

  /-
  @notice Burns tokens from an address.
  @param fromAddr Address whose balance is burned.
  @param amount Token amount to burn.
  @return True on success.
  -/
  function burn (fromAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balances fromAddr
    require (currentBalance >= amount) "Insufficient balance"
    let currentSupply ← getStorage tokenSupply
    require (currentSupply >= amount) "Insufficient supply"
    setMapping balances fromAddr (sub currentBalance amount)
    setStorage tokenSupply (sub currentSupply amount)
    emit "Transfer" [addressToWord fromAddr, addressToWord zeroAddress, amount]
    return true

namespace ERC20

abbrev contractOwner := ERC20Base.contractOwner
abbrev tokenSupply := ERC20Base.tokenSupply
abbrev balances := ERC20Base.balances
abbrev allowances := ERC20Base.allowances
abbrev maxUint256 := ERC20Base.maxUint256
abbrev tokenDecimals := ERC20Base.__verity_immutable_slot_tokenDecimals

abbrev decimals := ERC20Base.decimals
abbrev totalSupply := ERC20Base.totalSupply
abbrev balanceOf := ERC20Base.balanceOf
abbrev allowance := ERC20Base.allowance
abbrev owner := ERC20Base.owner
abbrev transferOwnership := ERC20Base.transferOwnership
abbrev renounceOwnership := ERC20Base.renounceOwnership
abbrev approve := ERC20Base.approve
abbrev transfer := ERC20Base.transfer
abbrev transferFrom := ERC20Base.transferFrom
abbrev mint := ERC20Base.mint
abbrev burn := ERC20Base.burn

def spec : Compiler.CompilationModel.CompilationModel :=
  { ERC20Base.spec with
    name := "ERC20"
    events := [
      Tamago.Common.Events.ownershipTransferred,
      Tamago.Common.Events.transfer,
      Tamago.Common.Events.approval
    ] }

end ERC20

end Tamago.Tokens
