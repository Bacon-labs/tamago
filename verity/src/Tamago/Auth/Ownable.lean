import Contracts.Common
import Tamago.Common.Events

namespace Tamago.Auth

open Verity hiding pure bind
open Contracts

/-
@title Ownable
@notice Single-owner authorization primitive with ownership transfer and renunciation.
@dev The constructor sets the initial owner directly. `transferOwnership` and
`renounceOwnership` are restricted to the current owner, and ownership changes
emit `OwnershipTransferred`.
-/
verity_contract OwnableBase where
  storage
    contractOwner : Address := slot 0

  errors
    error Unauthorized ()
    error NewOwnerIsZeroAddress ()

  /-
  @notice Initializes the contract owner.
  @param initialOwner Address that receives ownership at deployment.
  -/
  constructor (initialOwner : Address) := do
    setStorageAddr contractOwner initialOwner

  /-
  @notice Returns the current owner.
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
  @notice Renounces ownership and leaves the contract without an owner.
  @return True on success.
  -/
  function renounceOwnership () : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    requireError (sender == currentOwner) Unauthorized()
    setStorageAddr contractOwner zeroAddress
    emit "OwnershipTransferred" [addressToWord currentOwner, addressToWord zeroAddress]
    return true

namespace Ownable

abbrev contractOwner := OwnableBase.contractOwner

abbrev owner := OwnableBase.owner
abbrev transferOwnership := OwnableBase.transferOwnership
abbrev renounceOwnership := OwnableBase.renounceOwnership

def spec : Compiler.CompilationModel.CompilationModel :=
  { OwnableBase.spec with
    name := "Ownable"
    events := [Tamago.Common.Events.ownershipTransferred] }

end Ownable

end Tamago.Auth
