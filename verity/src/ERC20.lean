import Contracts.Common
import src.Ownable

namespace src

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract ERC20 where
  storage
    contractOwner : Address := slot 0
    tokenSupply : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
    allowances : Address → Address → Uint256 := slot 3

  constants
    maxUint256 : Uint256 := (sub 0 1)

  constructor (initialOwner : Address) := do
    setStorageAddr contractOwner initialOwner
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

  function view owner () : Address := do
    let currentOwner ← getStorageAddr contractOwner
    return currentOwner

  function transferOwnership (newOwner : Address) : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    require (newOwner != zeroAddress) "Invalid owner"
    setStorageAddr contractOwner newOwner
    return true

  function renounceOwnership () : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr contractOwner zeroAddress
    return true

  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount
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
    return true

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
    return true

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
    return true

end src
