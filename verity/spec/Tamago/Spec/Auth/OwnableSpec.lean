import Tamago.Auth.Ownable

namespace Tamago.Spec.Auth.OwnableSpec

open Verity
open Tamago.Auth.Ownable

/-
Ownable specs are organized by public function. Each function is described by
small properties for authorization, success cases, state updates, and frame
conditions.
-/

/-
owner()

Properties specified:
- The view returns exactly the address stored in the owner slot.

Security conclusions:
- Authorization checks below use the same owner value exposed by owner().
- A mismatch between the getter and authorization state would be caught at this
  base layer.
-/
def ownable_owner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr contractOwner.slot

/-
transferOwnership(newOwner)

Properties specified:
- A non-owner cannot transfer ownership.
- The current owner cannot transfer ownership to the zero address.
- A valid owner transfer succeeds and writes the new owner.
- No other address, integer, mapping, or array storage is changed.

Security conclusions:
- Ownership authority moves only by an explicit valid owner action.
- Zero-address ownership cannot be introduced by transferOwnership().
- The function cannot corrupt unrelated storage while moving authority.
-/
def ownable_transferOwnership_reverts_for_non_owner
    (_newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Unauthorized()" s

def ownable_transferOwnership_reverts_for_zero_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    newOwner = zeroAddress →
      result = ContractResult.revert "NewOwnerIsZeroAddress()" s

def ownable_transferOwnership_succeeds_for_owner_to_nonzero
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    newOwner ≠ zeroAddress →
      result = ContractResult.success true result.snd

def ownable_transferOwnership_sets_new_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    newOwner ≠ zeroAddress →
      result.snd.storageAddr contractOwner.slot = newOwner

def ownable_transferOwnership_keeps_other_owner_slots
    (_newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ∀ slotIdx, slotIdx ≠ contractOwner.slot →
    result.snd.storageAddr slotIdx = s.storageAddr slotIdx

def ownable_transferOwnership_keeps_uint_storage
    (_newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage

def ownable_transferOwnership_keeps_balances_and_allowances
    (_newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storageMap = s.storageMap ∧
  result.snd.storageMapUint = s.storageMapUint ∧
  result.snd.storageMap2 = s.storageMap2

def ownable_transferOwnership_keeps_array_storage
    (_newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storageArray = s.storageArray

/-
renounceOwnership()

Properties specified:
- A non-owner cannot renounce ownership.
- The current owner can renounce successfully.
- A successful renounce clears the owner slot to the zero address.
- No other address, integer, mapping, or array storage is changed.

Security conclusions:
- Ownership can be disabled only by the current owner.
- Renouncing ownership clears authority rather than transferring it to an
  unintended address.
- The function cannot corrupt unrelated storage while clearing authority.
-/
def ownable_renounceOwnership_reverts_for_non_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Unauthorized()" s

def ownable_renounceOwnership_succeeds_for_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    result = ContractResult.success true result.snd

def ownable_renounceOwnership_clears_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    result.snd.storageAddr contractOwner.slot = zeroAddress

def ownable_renounceOwnership_keeps_other_owner_slots
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ∀ slotIdx, slotIdx ≠ contractOwner.slot →
    result.snd.storageAddr slotIdx = s.storageAddr slotIdx

def ownable_renounceOwnership_keeps_uint_storage
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage

def ownable_renounceOwnership_keeps_balances_and_allowances
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storageMap = s.storageMap ∧
  result.snd.storageMapUint = s.storageMapUint ∧
  result.snd.storageMap2 = s.storageMap2

def ownable_renounceOwnership_keeps_array_storage
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storageArray = s.storageArray

end Tamago.Spec.Auth.OwnableSpec
