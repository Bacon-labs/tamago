import Contracts.Common

namespace src

open Verity hiding pure bind
open Contracts

verity_contract Ownable where
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
    return true

  function renounceOwnership () : Bool := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr contractOwner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr contractOwner zeroAddress
    return true

end src
