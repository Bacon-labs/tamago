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

  errors
    error Unauthorized ()
    error NewOwnerIsZeroAddress ()
    error BalanceQueryForZeroAddress ()
    error TokenDoesNotExist ()
    error NotOwnerNorApproved ()
    error TransferToZeroAddress ()
    error TokenAlreadyExists ()
    error TransferFromIncorrectOwner ()
    error InsufficientBalance ()
    error AccountBalanceOverflow ()
    error TotalSupplyOverflow ()

  /-
  @notice Initializes token ownership, supply, and token ID tracking.
  @param initialOwner Address that receives ownership at deployment.
  -/
  constructor (initialOwner : Address) := do
    setStorageAddr contractOwner initialOwner
    setStorage tokenSupply 0
    setStorage nextTokenId 0

  /-
  @notice Returns the total number of minted tokens.
  @return Current total supply.
  -/
  function view totalSupply () : Uint256 := do
    let currentSupply ← getStorage tokenSupply
    return currentSupply

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
    requireError (sender == currentOwner) Unauthorized()
    requireError (newOwner != zeroAddress) NewOwnerIsZeroAddress()
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
    requireError (sender == currentOwner) Unauthorized()
    setStorageAddr contractOwner zeroAddress
    emit "OwnershipTransferred" [addressToWord currentOwner, addressToWord zeroAddress]
    return true

  /-
  @notice Returns the number of tokens owned by an address.
  @param account Owner address to query.
  @return Current token balance for `account`.
  -/
  function view balanceOf (account : Address) : Uint256 := do
    requireError (account != zeroAddress) BalanceQueryForZeroAddress()
    let currentBalance ← getMapping balances account
    return currentBalance

  /-
  @notice Returns the owner of a token.
  @param tokenId Token ID to query.
  @return Address that owns `tokenId`.
  -/
  function view ownerOf (tokenId : Uint256) : Address := do
    let ownerWord ← getMappingUint tokenOwners tokenId
    requireError (ownerWord != 0) TokenDoesNotExist()
    return wordToAddress ownerWord

  /-
  @notice Returns the approved spender for a token.
  @param tokenId Token ID to query.
  @return Address approved for `tokenId`.
  -/
  function view getApproved (tokenId : Uint256) : Address := do
    let ownerWord ← getMappingUint tokenOwners tokenId
    requireError (ownerWord != 0) TokenDoesNotExist()
    let approvedAddr ← getMappingUintAddr tokenApprovals tokenId
    return approvedAddr

  /-
  @notice Returns whether an operator is approved for all of an owner's tokens.
  @param ownerAddr Token owner address.
  @param operator Operator address to query.
  @return True if `operator` is approved for all tokens owned by `ownerAddr`.
  -/
  function view isApprovedForAll (ownerAddr : Address, operator : Address) : Bool := do
    let flag ← getMapping2 operatorApprovals ownerAddr operator
    return flag != 0

  /-
  @notice Approves an address to transfer a token.
  @param approved Address approved for the token.
  @param tokenId Token ID whose approval is updated.
  @return True on success.
  -/
  function approve (approved : Address, tokenId : Uint256) : Bool := do
    let sender ← msgSender
    let ownerWord ← getMappingUint tokenOwners tokenId
    requireError (ownerWord != 0) TokenDoesNotExist()
    let tokenOwner := wordToAddress ownerWord
    let operatorFlag ← getMapping2 operatorApprovals tokenOwner sender
    requireError ((sender == tokenOwner) || (operatorFlag != 0)) NotOwnerNorApproved()
    setMappingUintAddr tokenApprovals tokenId approved
    emit "Approval" [addressToWord tokenOwner, addressToWord approved, tokenId]
    return true

  /-
  @notice Sets or clears an operator approval for all caller-owned tokens.
  @param operator Operator address.
  @param approved Whether the operator is approved.
  @return True on success.
  -/
  function setApprovalForAll (operator : Address, approved : Bool) : Bool := do
    let sender ← msgSender
    setMapping2 operatorApprovals sender operator (boolToWord approved)
    emit "ApprovalForAll" [addressToWord sender, addressToWord operator, boolToWord approved]
    return true

  /-
  @notice Mints the next sequential token ID to an address.
  @param toAddr Address that receives the minted token.
  @return Minted token ID.
  -/
  function mint (toAddr : Address) : Uint256 := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    requireError (sender == currentOwner) Unauthorized()
    requireError (toAddr != zeroAddress) TransferToZeroAddress()

    let tokenId ← getStorage nextTokenId
    let currentOwnerWord ← getMappingUint tokenOwners tokenId
    requireError (currentOwnerWord == 0) TokenAlreadyExists()

    let recipientBalance ← getMapping balances toAddr
    let newRecipientBalance ← requireSomeUintError (safeAdd recipientBalance 1) AccountBalanceOverflow()
    let currentSupply ← getStorage tokenSupply
    let newSupply ← requireSomeUintError (safeAdd currentSupply 1) TotalSupplyOverflow()

    setMappingUintAddr tokenOwners tokenId toAddr
    setMapping balances toAddr newRecipientBalance
    setStorage tokenSupply newSupply
    setStorage nextTokenId (add tokenId 1)
    emit "Transfer" [addressToWord zeroAddress, addressToWord toAddr, tokenId]
    return tokenId

  /-
  @notice Transfers a token between addresses.
  @param fromAddr Current token owner.
  @param toAddr Recipient address.
  @param tokenId Token ID to transfer.
  @return True on success.
  -/
  function transferFrom (fromAddr : Address, toAddr : Address, tokenId : Uint256) : Bool := do
    let sender ← msgSender
    requireError (toAddr != zeroAddress) TransferToZeroAddress()

    let ownerWord ← getMappingUint tokenOwners tokenId
    requireError (ownerWord != 0) TokenDoesNotExist()

    let fromWord := addressToWord fromAddr
    requireError (ownerWord == fromWord) TransferFromIncorrectOwner()

    let approvedWord ← getMappingUint tokenApprovals tokenId
    let operatorWord ← getMapping2 operatorApprovals fromAddr sender
    let senderWord := addressToWord sender
    let authorized := (sender == fromAddr) || (approvedWord == senderWord) || (operatorWord != 0)
    requireError authorized NotOwnerNorApproved()

    if fromAddr == toAddr then
      pure ()
    else
      let fromBalance ← getMapping balances fromAddr
      requireError (fromBalance >= 1) InsufficientBalance()
      let toBalance ← getMapping balances toAddr
      let newToBalance ← requireSomeUintError (safeAdd toBalance 1) AccountBalanceOverflow()
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
