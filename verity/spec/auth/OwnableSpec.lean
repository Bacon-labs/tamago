import src.auth.Ownable

namespace spec.auth.OwnableSpec

open Verity
open src.auth.Ownable

def ownable_owner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr contractOwner.slot

def ownable_transferOwnership_effect
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s) ∧
  (s.sender = s.storageAddr contractOwner.slot →
    (newOwner = zeroAddress →
      result = ContractResult.revert "Invalid owner" s) ∧
    (newOwner ≠ zeroAddress →
      result = ContractResult.success true result.snd ∧
      result.snd.storageAddr contractOwner.slot = newOwner ∧
      (∀ slotIdx, slotIdx ≠ contractOwner.slot →
        result.snd.storageAddr slotIdx = s.storageAddr slotIdx) ∧
      result.snd.storage = s.storage ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storageMapUint = s.storageMapUint ∧
      result.snd.storageMap2 = s.storageMap2 ∧
      result.snd.storageArray = s.storageArray))

def ownable_renounceOwnership_effect
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s) ∧
  (s.sender = s.storageAddr contractOwner.slot →
    result = ContractResult.success true result.snd ∧
    result.snd.storageAddr contractOwner.slot = zeroAddress ∧
    (∀ slotIdx, slotIdx ≠ contractOwner.slot →
      result.snd.storageAddr slotIdx = s.storageAddr slotIdx) ∧
    result.snd.storage = s.storage ∧
    result.snd.storageMap = s.storageMap ∧
    result.snd.storageMapUint = s.storageMapUint ∧
    result.snd.storageMap2 = s.storageMap2 ∧
    result.snd.storageArray = s.storageArray)

end spec.auth.OwnableSpec
