import Contracts.Common
import common.Events

namespace src.tokens

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract WETHBase where
  storage
    tokenSupply : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
    allowances : Address → Address → Uint256 := slot 3

  constants
    maxUint256 : Uint256 := (sub 0 1)

  constructor () := do
    setStorage tokenSupply 0

  function view decimals () : Uint256 := do
    return 18

  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage tokenSupply
    return currentSupply

  function view balanceOf (account : Address) : Uint256 := do
    let currentBalance ← getMapping balances account
    return currentBalance

  function view allowance (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowances ownerAddr spender
    return currentAllowance

  function payable deposit () : Bool := do
    let sender ← msgSender
    let value ← msgValue
    let currentBalance ← getMapping balances sender
    let newBalance ← requireSomeUint (safeAdd currentBalance value) "Balance overflow"
    let currentSupply ← getStorage tokenSupply
    let newSupply ← requireSomeUint (safeAdd currentSupply value) "Supply overflow"
    setMapping balances sender newBalance
    setStorage tokenSupply newSupply
    emit "Transfer" [addressToWord zeroAddress, addressToWord sender, value]
    emit "Deposit" [addressToWord sender, value]
    return true

  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount
    emit "Approval" [addressToWord sender, addressToWord spender, amount]
    return true

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

  function withdraw (amount : Uint256) : Bool := do
    let sender ← msgSender
    let currentBalance ← getMapping balances sender
    require (currentBalance >= amount) "Insufficient balance"
    let currentSupply ← getStorage tokenSupply
    require (currentSupply >= amount) "Insufficient supply"
    setMapping balances sender (sub currentBalance amount)
    setStorage tokenSupply (sub currentSupply amount)
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
      common.Events.transfer,
      common.Events.approval,
      common.Events.wethDeposit,
      common.Events.wethWithdrawal
    ] }

end WETH

end src.tokens
