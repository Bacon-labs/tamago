import Contracts.Common
import src.Ownable

namespace src

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

@[simp] def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

verity_contract ERC721 where
  storage
    contractOwner : Address := slot 0
    tokenSupply : Uint256 := slot 1
    nextTokenId : Uint256 := slot 2
    balances : Address → Uint256 := slot 3
    tokenOwners : Uint256 → Uint256 := slot 4
    tokenApprovals : Uint256 → Uint256 := slot 5
    operatorApprovals : Address → Address → Uint256 := slot 6

  constructor (initialOwner : Address) := do
    setStorageAddr contractOwner initialOwner
    setStorage tokenSupply 0
    setStorage nextTokenId 0

  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage tokenSupply
    return currentSupply

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

  function view balanceOf (account : Address) : Uint256 := do
    require (account != zeroAddress) "Invalid owner"
    let currentBalance ← getMapping balances account
    return currentBalance

  function view ownerOf (tokenId : Uint256) : Address := do
    let ownerWord ← getMappingUint tokenOwners tokenId
    require (ownerWord != 0) "Token does not exist"
    return wordToAddress ownerWord

  function view getApproved (tokenId : Uint256) : Address := do
    let ownerWord ← getMappingUint tokenOwners tokenId
    require (ownerWord != 0) "Token does not exist"
    let approvedAddr ← getMappingUintAddr tokenApprovals tokenId
    return approvedAddr

  function view isApprovedForAll (ownerAddr : Address, operator : Address) : Bool := do
    let flag ← getMapping2 operatorApprovals ownerAddr operator
    return flag != 0

  function approve (approved : Address, tokenId : Uint256) : Bool := do
    let sender ← msgSender
    let ownerWord ← getMappingUint tokenOwners tokenId
    require (ownerWord != 0) "Token does not exist"
    let tokenOwner := wordToAddress ownerWord
    let operatorFlag ← getMapping2 operatorApprovals tokenOwner sender
    require ((sender == tokenOwner) || (operatorFlag != 0)) "Not authorized"
    setMappingUintAddr tokenApprovals tokenId approved
    return true

  function setApprovalForAll (operator : Address, approved : Bool) : Bool := do
    let sender ← msgSender
    setMapping2 operatorApprovals sender operator (boolToWord approved)
    return true

  function mint (toAddr : Address) : Uint256 := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    require (toAddr != zeroAddress) "Invalid recipient"

    let tokenId ← getStorage nextTokenId
    let currentOwnerWord ← getMappingUint tokenOwners tokenId
    require (currentOwnerWord == 0) "Token already minted"

    let recipientBalance ← getMapping balances toAddr
    let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance 1) "Balance overflow"
    let currentSupply ← getStorage tokenSupply
    let newSupply ← requireSomeUint (safeAdd currentSupply 1) "Supply overflow"

    setMappingUintAddr tokenOwners tokenId toAddr
    setMapping balances toAddr newRecipientBalance
    setStorage tokenSupply newSupply
    setStorage nextTokenId (add tokenId 1)
    return tokenId

  function transferFrom (fromAddr : Address, toAddr : Address, tokenId : Uint256) : Bool := do
    let sender ← msgSender
    require (toAddr != zeroAddress) "Invalid recipient"

    let ownerWord ← getMappingUint tokenOwners tokenId
    require (ownerWord != 0) "Token does not exist"

    let fromWord := addressToWord fromAddr
    require (ownerWord == fromWord) "From is not owner"

    let approvedWord ← getMappingUint tokenApprovals tokenId
    let operatorWord ← getMapping2 operatorApprovals fromAddr sender
    let senderWord := addressToWord sender
    let authorized := (sender == fromAddr) || (approvedWord == senderWord) || (operatorWord != 0)
    require authorized "Not authorized"

    if fromAddr == toAddr then
      pure ()
    else
      let fromBalance ← getMapping balances fromAddr
      require (fromBalance >= 1) "Insufficient balance"
      let toBalance ← getMapping balances toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance 1) "Balance overflow"
      setMapping balances fromAddr (sub fromBalance 1)
      setMapping balances toAddr newToBalance

    setMappingUintAddr tokenOwners tokenId toAddr
    setMappingUintAddr tokenApprovals tokenId zeroAddress
    return true

end src
