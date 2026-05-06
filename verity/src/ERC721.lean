import Contracts.Common

namespace src

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

@[simp] def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

verity_contract ERC721 where
  storage
    ownerSlot : Address := slot 0
    totalSupplySlot : Uint256 := slot 1
    nextTokenIdSlot : Uint256 := slot 2
    balancesSlot : Address → Uint256 := slot 3
    ownersSlot : Uint256 → Uint256 := slot 4
    tokenApprovalsSlot : Uint256 → Uint256 := slot 5
    operatorApprovalsSlot : Address → Address → Uint256 := slot 6

  constructor (initialOwner : Address) := do
    setStorageAddr ownerSlot initialOwner
    setStorage totalSupplySlot 0
    setStorage nextTokenIdSlot 0

  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function view owner () : Address := do
    let currentOwner ← getStorageAddr ownerSlot
    return currentOwner

  function view balanceOf (account : Address) : Uint256 := do
    require (account != zeroAddress) "Invalid owner"
    let currentBalance ← getMapping balancesSlot account
    return currentBalance

  function view ownerOf (tokenId : Uint256) : Address := do
    let ownerWord ← getMappingUint ownersSlot tokenId
    require (ownerWord != 0) "Token does not exist"
    return wordToAddress ownerWord

  function view getApproved (tokenId : Uint256) : Address := do
    let ownerWord ← getMappingUint ownersSlot tokenId
    require (ownerWord != 0) "Token does not exist"
    let approvedAddr ← getMappingUintAddr tokenApprovalsSlot tokenId
    return approvedAddr

  function view isApprovedForAll (ownerAddr : Address, operator : Address) : Bool := do
    let flag ← getMapping2 operatorApprovalsSlot ownerAddr operator
    return flag != 0

  function approve (approved : Address, tokenId : Uint256) : Bool := do
    let sender ← msgSender
    let ownerWord ← getMappingUint ownersSlot tokenId
    require (ownerWord != 0) "Token does not exist"
    let tokenOwner := wordToAddress ownerWord
    let operatorFlag ← getMapping2 operatorApprovalsSlot tokenOwner sender
    require ((sender == tokenOwner) || (operatorFlag != 0)) "Not authorized"
    setMappingUintAddr tokenApprovalsSlot tokenId approved
    return true

  function setApprovalForAll (operator : Address, approved : Bool) : Bool := do
    let sender ← msgSender
    setMapping2 operatorApprovalsSlot sender operator (boolToWord approved)
    return true

  function mint (toAddr : Address) : Uint256 := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    require (toAddr != zeroAddress) "Invalid recipient"

    let tokenId ← getStorage nextTokenIdSlot
    let currentOwnerWord ← getMappingUint ownersSlot tokenId
    require (currentOwnerWord == 0) "Token already minted"

    let recipientBalance ← getMapping balancesSlot toAddr
    let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance 1) "Balance overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply 1) "Supply overflow"

    setMappingUintAddr ownersSlot tokenId toAddr
    setMapping balancesSlot toAddr newRecipientBalance
    setStorage totalSupplySlot newSupply
    setStorage nextTokenIdSlot (add tokenId 1)
    return tokenId

  function transferFrom (fromAddr : Address, toAddr : Address, tokenId : Uint256) : Bool := do
    let sender ← msgSender
    require (toAddr != zeroAddress) "Invalid recipient"

    let ownerWord ← getMappingUint ownersSlot tokenId
    require (ownerWord != 0) "Token does not exist"

    let fromWord := addressToWord fromAddr
    require (ownerWord == fromWord) "From is not owner"

    let approvedWord ← getMappingUint tokenApprovalsSlot tokenId
    let operatorWord ← getMapping2 operatorApprovalsSlot fromAddr sender
    let senderWord := addressToWord sender
    let authorized := (sender == fromAddr) || (approvedWord == senderWord) || (operatorWord != 0)
    require authorized "Not authorized"

    if fromAddr == toAddr then
      pure ()
    else
      let fromBalance ← getMapping balancesSlot fromAddr
      require (fromBalance >= 1) "Insufficient balance"
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance 1) "Balance overflow"
      setMapping balancesSlot fromAddr (sub fromBalance 1)
      setMapping balancesSlot toAddr newToBalance

    setMappingUintAddr ownersSlot tokenId toAddr
    setMappingUintAddr tokenApprovalsSlot tokenId zeroAddress
    return true

end src
