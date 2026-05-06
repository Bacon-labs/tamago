import Contracts.Common

namespace src

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract WETH where
  storage
    totalSupplySlot : Uint256 := slot 0
    balancesSlot : Address → Uint256 := slot 1
    allowancesSlot : Address → Address → Uint256 := slot 2

  constructor () := do
    setStorage totalSupplySlot 0

  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function view balanceOf (account : Address) : Uint256 := do
    let currentBalance ← getMapping balancesSlot account
    return currentBalance

  function view allowance (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowancesSlot ownerAddr spender
    return currentAllowance

  function payable deposit () : Bool := do
    let sender ← msgSender
    let value ← msgValue
    let currentBalance ← getMapping balancesSlot sender
    let newBalance ← requireSomeUint (safeAdd currentBalance value) "Balance overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply value) "Supply overflow"
    setMapping balancesSlot sender newBalance
    setStorage totalSupplySlot newSupply
    return true

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

  function withdraw (amount : Uint256)
    local_obligations [native_eth_call_refinement := proved "The proof obligations for WETH withdraw cover all storage accounting around the generated low-level call; no storage writes occur after the interaction."]
    : Bool := do
    let sender ← msgSender
    let currentBalance ← getMapping balancesSlot sender
    require (currentBalance >= amount) "Insufficient balance"
    let currentSupply ← getStorage totalSupplySlot
    require (currentSupply >= amount) "Insufficient supply"
    setMapping balancesSlot sender (sub currentBalance amount)
    setStorage totalSupplySlot (sub currentSupply amount)
    return true

end src
