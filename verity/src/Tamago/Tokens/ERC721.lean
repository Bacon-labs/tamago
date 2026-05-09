import Contracts.Common
import Tamago.Auth.Ownable
import Tamago.Common.Events

namespace Tamago.Tokens

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

@[simp] def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

/-
@title ERC721
@notice Non-fungible token with owner-controlled minting, approvals, operator
approvals, and transfer behavior.
@dev Token IDs are minted sequentially from `nextTokenId`. Ownership and
approval state follow the core ERC721 transfer authorization model.
Limitations: metadata functions such as `name()`, `symbol()`, and `tokenURI()`
are not implemented, and safe transfer entrypoints such as `safeTransferFrom()`
are not implemented.
-/
verity_contract ERC721Base where
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
    emit "OwnershipTransferred" [addressToWord currentOwner, addressToWord newOwner]
    return true

  function renounceOwnership () : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr contractOwner zeroAddress
    emit "OwnershipTransferred" [addressToWord currentOwner, addressToWord zeroAddress]
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
    emit "Approval" [addressToWord tokenOwner, addressToWord approved, tokenId]
    return true

  function setApprovalForAll (operator : Address, approved : Bool) : Bool := do
    let sender ← msgSender
    setMapping2 operatorApprovals sender operator (boolToWord approved)
    emit "ApprovalForAll" [addressToWord sender, addressToWord operator, boolToWord approved]
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
    emit "Transfer" [addressToWord zeroAddress, addressToWord toAddr, tokenId]
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
    emit "Transfer" [addressToWord fromAddr, addressToWord toAddr, tokenId]
    return true

namespace ERC721

abbrev contractOwner := ERC721Base.contractOwner
abbrev tokenSupply := ERC721Base.tokenSupply
abbrev nextTokenId := ERC721Base.nextTokenId
abbrev balances := ERC721Base.balances
abbrev tokenOwners := ERC721Base.tokenOwners
abbrev tokenApprovals := ERC721Base.tokenApprovals
abbrev operatorApprovals := ERC721Base.operatorApprovals

abbrev totalSupply := ERC721Base.totalSupply
abbrev owner := ERC721Base.owner
abbrev transferOwnership := ERC721Base.transferOwnership
abbrev renounceOwnership := ERC721Base.renounceOwnership
abbrev balanceOf := ERC721Base.balanceOf
abbrev ownerOf := ERC721Base.ownerOf
abbrev getApproved := ERC721Base.getApproved
abbrev isApprovedForAll := ERC721Base.isApprovedForAll
abbrev approve := ERC721Base.approve
abbrev setApprovalForAll := ERC721Base.setApprovalForAll
abbrev mint := ERC721Base.mint
abbrev transferFrom := ERC721Base.transferFrom

def spec : Compiler.CompilationModel.CompilationModel :=
  { ERC721Base.spec with
    name := "ERC721"
    events := [
      Tamago.Common.Events.ownershipTransferred,
      Tamago.Common.Events.erc721Transfer,
      Tamago.Common.Events.erc721Approval,
      Tamago.Common.Events.approvalForAll
    ] }

end ERC721

end Tamago.Tokens
