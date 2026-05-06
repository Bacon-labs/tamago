import Contracts.Common

namespace src

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract ERC20 where
  storage
    ownerSlot : Address := slot 0
    totalSupplySlot : Uint256 := slot 1
    balancesSlot : Address → Uint256 := slot 2
    allowancesSlot : Address → Address → Uint256 := slot 3

  constructor (initialOwner : Address) := do
    setStorageAddr ownerSlot initialOwner
    setStorage totalSupplySlot 0

  function view decimals () : Uint256 := do
    return 18

  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function view balanceOf (account : Address) : Uint256 := do
    let currentBalance ← getMapping balancesSlot account
    return currentBalance

  function view allowance (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowancesSlot ownerAddr spender
    return currentAllowance

  function view owner () : Address := do
    let currentOwner ← getStorageAddr ownerSlot
    return currentOwner

  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowancesSlot sender spender amount
    return true

  function transfer (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let senderBalance ← getMapping balancesSlot sender
    require (senderBalance >= amount) "Insufficient balance"
    if sender == toAddr then
      pure ()
    else
      let recipientBalance ← getMapping balancesSlot toAddr
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balancesSlot sender (sub senderBalance amount)
      setMapping balancesSlot toAddr newRecipientBalance
    return true

  function transferFrom (fromAddr : Address, toAddr : Address, amount : Uint256) : Bool := do
    let spender ← msgSender
    let currentAllowance ← getMapping2 allowancesSlot fromAddr spender
    require (currentAllowance >= amount) "Insufficient allowance"
    let fromBalance ← getMapping balancesSlot fromAddr
    require (fromBalance >= amount) "Insufficient balance"

    if fromAddr == toAddr then
      pure ()
    else
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "Recipient balance overflow"
      setMapping balancesSlot fromAddr (sub fromBalance amount)
      setMapping balancesSlot toAddr newToBalance

    if currentAllowance == 115792089237316195423570985008687907853269984665640564039457584007913129639935 then
      pure ()
    else
      setMapping2 allowancesSlot fromAddr spender (sub currentAllowance amount)
    return true

  function mint (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balancesSlot toAddr
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balancesSlot toAddr newBalance
    setStorage totalSupplySlot newSupply
    return true

  function burn (fromAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balancesSlot fromAddr
    require (currentBalance >= amount) "Insufficient balance"
    let currentSupply ← getStorage totalSupplySlot
    require (currentSupply >= amount) "Insufficient supply"
    setMapping balancesSlot fromAddr (sub currentBalance amount)
    setStorage totalSupplySlot (sub currentSupply amount)
    return true

end src
