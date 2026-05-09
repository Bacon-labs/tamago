import Contracts.Common
import Tamago.Common.Events

namespace Tamago.Auth

open Verity hiding pure bind
open Contracts

verity_contract OwnableBase where
  storage
    contractOwner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr contractOwner initialOwner

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
