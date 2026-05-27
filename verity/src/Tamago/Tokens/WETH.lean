import Contracts.Common
import Compiler.ECM
import Tamago.Common.Events

namespace Tamago.Tokens

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Compiler.Yul

namespace WETHNative

/--
Lean-side model for sending native ETH out of the contract.

The compiler model below delegates the native value transfer to a named ECM.
The source semantics additionally records the contract's native balance
decrease when that call reports success, so specs can state exact ETH-balance
effects instead of only wrapped-token accounting.
-/
def transfer (toAddr : Address) (amount : Uint256) : Contract Uint256 :=
  fun state =>
    let sent := call 50000 (addressToWord toAddr) amount 0 0 0 0
    if sent == 0 then
      ContractResult.success sent state
    else
      ContractResult.success sent { state with selfBalance := sub state.selfBalance amount }

def nativeTransferModule : Compiler.ECM.ExternalCallModule where
  name := "nativeEthTransfer"
  numArgs := 2
  resultVars := ["sent"]
  writesState := true
  readsState := true
  axioms := ["native_eth_transfer_interface"]
  compile := fun _ctx args => do
    let (toExpr, amountExpr) ← match args with
      | [toExpr, amountExpr] => pure (toExpr, amountExpr)
      | _ => throw "nativeEthTransfer expects 2 arguments (to, amount)"
    pure [
      YulStmt.let_ "sent" (YulExpr.call "call" [
        YulExpr.lit 50000,
        toExpr,
        amountExpr,
        YulExpr.lit 0,
        YulExpr.lit 0,
        YulExpr.lit 0,
        YulExpr.lit 0
      ])
    ]

def transfer_model : Compiler.CompilationModel.FunctionSpec := {
  name := "wethNativeTransfer"
  params := [
    { name := "toAddr", ty := Compiler.CompilationModel.ParamType.address },
    { name := "amount", ty := Compiler.CompilationModel.ParamType.uint256 }
  ]
  returnType := some Compiler.CompilationModel.FieldType.uint256
  returns := [Compiler.CompilationModel.ParamType.uint256]
  body := [
    Compiler.CompilationModel.Stmt.ecm nativeTransferModule [
      Compiler.CompilationModel.Expr.param "toAddr",
      Compiler.CompilationModel.Expr.param "amount"
    ],
    Compiler.CompilationModel.Stmt.return
      (Compiler.CompilationModel.Expr.localVar "sent")
  ]
}

end WETHNative

/-
@title WETH
@notice Wrapped ETH token with ERC20-compatible balances, allowances, deposits,
withdrawals, and transfers.
@dev Deposits mint wrapped balances for `msg.value`; withdrawals burn wrapped
balances and perform a native ETH transfer to the caller. The native transfer is
modeled through an explicit external call module for auditing.
Limitations: metadata accessors `name()` and `symbol()` are intentionally not
implemented, and ETH wrapping is exposed through `deposit()` rather than a
receive or fallback entrypoint.
-/
verity_contract WETHBase where
  storage
    tokenSupply : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
    allowances : Address → Address → Uint256 := slot 3

  errors
    error InsufficientBalance ()
    error InsufficientAllowance ()
    error BalanceOverflow ()
    error TotalSupplyOverflow ()
    error InsufficientSupply ()
    error InsufficientEthBacking ()
    error EthTransferFailed ()

  constants
    maxUint256 : Uint256 := (sub 0 1)

  /-
  @notice Initializes wrapped token supply to zero.
  -/
  constructor () := do
    setStorage tokenSupply 0

  /-
  @notice Returns the token decimal precision.
  @return Fixed decimal precision of 18.
  -/
  function view decimals () : Uint256 := do
    return 18

  /-
  @notice Returns the total wrapped token supply.
  @return Current total supply.
  -/
  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage tokenSupply
    return currentSupply

  /-
  @notice Returns an account's wrapped ETH balance.
  @param account Address whose balance is queried.
  @return Current wrapped token balance for `account`.
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
  @notice Wraps the caller's attached ETH into WETH.
  @return True on success.
  -/
  function payable deposit () : Bool := do
    let sender ← msgSender
    let value ← msgValue
    let currentBalance ← getMapping balances sender
    let newBalance ← requireSomeUintError (safeAdd currentBalance value) BalanceOverflow()
    let currentSupply ← getStorage tokenSupply
    let newSupply ← requireSomeUintError (safeAdd currentSupply value) TotalSupplyOverflow()
    setMapping balances sender newBalance
    setStorage tokenSupply newSupply
    emit "Transfer" [addressToWord zeroAddress, addressToWord sender, value]
    emit "Deposit" [addressToWord sender, value]
    return true

  /-
  @notice Sets the caller's allowance for a spender.
  @param spender Address allowed to spend the caller's WETH.
  @param amount Allowance amount to set.
  @return True on success.
  -/
  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount
    emit "Approval" [addressToWord sender, addressToWord spender, amount]
    return true

  /-
  @notice Transfers WETH from the caller to another address.
  @param toAddr Recipient address.
  @param amount WETH amount to transfer.
  @return True on success.
  -/
  function transfer (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let senderBalance ← getMapping balances sender
    requireError (senderBalance >= amount) InsufficientBalance()
    if sender == toAddr then
      pure ()
    else
      let recipientBalance ← getMapping balances toAddr
      let newRecipientBalance ← requireSomeUintError (safeAdd recipientBalance amount) BalanceOverflow()
      setMapping balances sender (sub senderBalance amount)
      setMapping balances toAddr newRecipientBalance
    emit "Transfer" [addressToWord sender, addressToWord toAddr, amount]
    return true

  /-
  @notice Transfers WETH from an approved owner to another address.
  @param fromAddr Address whose WETH balance is debited.
  @param toAddr Recipient address.
  @param amount WETH amount to transfer.
  @return True on success.
  -/
  function transferFrom (fromAddr : Address, toAddr : Address, amount : Uint256) : Bool := do
    let spender ← msgSender
    let currentAllowance ← getMapping2 allowances fromAddr spender
    requireError (currentAllowance >= amount) InsufficientAllowance()
    let fromBalance ← getMapping balances fromAddr
    requireError (fromBalance >= amount) InsufficientBalance()

    if fromAddr == toAddr then
      pure ()
    else
      let toBalance ← getMapping balances toAddr
      let newToBalance ← requireSomeUintError (safeAdd toBalance amount) BalanceOverflow()
      setMapping balances fromAddr (sub fromBalance amount)
      setMapping balances toAddr newToBalance

    if currentAllowance == maxUint256 then
      pure ()
    else
      setMapping2 allowances fromAddr spender (sub currentAllowance amount)
    emit "Transfer" [addressToWord fromAddr, addressToWord toAddr, amount]
    return true

  /-
  @notice Unwraps WETH and transfers native ETH to the caller.
  @param amount WETH amount to burn and withdraw.
  @return True on success.
  -/
  function withdraw (amount : Uint256) : Bool := do
    let sender ← msgSender
    let currentBalance ← getMapping balances sender
    requireError (currentBalance >= amount) InsufficientBalance()
    let currentSupply ← getStorage tokenSupply
    requireError (currentSupply >= amount) InsufficientSupply()
    let currentEth ← selfBalance
    requireError (currentEth >= amount) InsufficientEthBacking()
    setMapping balances sender (sub currentBalance amount)
    setStorage tokenSupply (sub currentSupply amount)
    let sent ← WETHNative.transfer sender amount
    requireError (sent != 0) EthTransferFailed()
    emit "Transfer" [addressToWord sender, addressToWord zeroAddress, amount]
    emit "Withdrawal" [addressToWord sender, amount]
    return true

namespace WETH

abbrev tokenSupply := WETHBase.tokenSupply
abbrev balances := WETHBase.balances
abbrev allowances := WETHBase.allowances
abbrev maxUint256 := WETHBase.maxUint256

abbrev decimals := WETHBase.decimals
abbrev totalSupply := WETHBase.totalSupply
abbrev balanceOf := WETHBase.balanceOf
abbrev allowance := WETHBase.allowance
abbrev deposit := WETHBase.deposit
abbrev approve := WETHBase.approve
abbrev transfer := WETHBase.transfer
abbrev transferFrom := WETHBase.transferFrom
abbrev withdraw := WETHBase.withdraw

def spec : Compiler.CompilationModel.CompilationModel :=
  { WETHBase.spec with
    name := "WETH"
    events := [
      Tamago.Common.Events.transfer,
      Tamago.Common.Events.approval,
      Tamago.Common.Events.wethDeposit,
      Tamago.Common.Events.wethWithdrawal
    ] }

end WETH

end Tamago.Tokens
