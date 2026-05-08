import Tamago.Spec.Auth.OwnableSpec
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Auth.OwnableProof

set_option linter.unusedSimpArgs false

open Verity
open Tamago.Spec.Auth.OwnableSpec
open Tamago.Auth.Ownable

attribute [local simp] contractOwner Tamago.Auth.OwnableBase.contractOwner
  Tamago.Auth.OwnableBase.owner Tamago.Auth.OwnableBase.transferOwnership Tamago.Auth.OwnableBase.renounceOwnership
  Contracts.emit emitEvent

-- tama: discharges=ownable_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  ownable_owner_spec ((owner).run s).fst s := by
  simp [ownable_owner_spec, owner, contractOwner, Bind.bind, Pure.pure]

private theorem transferOwnership_properties_after_run (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_reverts_for_non_owner newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_reverts_for_zero_owner newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_succeeds_for_owner_to_nonzero newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_sets_new_owner newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_keeps_other_owner_slots newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_keeps_uint_storage newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_keeps_balances_and_allowances newOwner s ((transferOwnership newOwner).run s) ∧
  ownable_transferOwnership_keeps_array_storage newOwner s ((transferOwnership newOwner).run s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa [contractOwner] using h_not_owner
    simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_owner_raw,
      ownable_transferOwnership_reverts_for_non_owner]
  · intro h_owner h_zero
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    have h_zero_raw : newOwner = 0 := by
      simpa [zeroAddress] using h_zero
    subst h_zero_raw
    simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
      Contract.run, Verity.bind, Bind.bind, Verity.require, h_owner_raw,
      ownable_transferOwnership_reverts_for_zero_owner]
  · intro h_owner h_nonzero
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    have h_nonzero_raw : newOwner ≠ 0 := by
      simpa [zeroAddress] using h_nonzero
    simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
      setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw,
      ownable_transferOwnership_succeeds_for_owner_to_nonzero]
  · intro h_owner h_nonzero
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    have h_nonzero_raw : newOwner ≠ 0 := by
      simpa [zeroAddress] using h_nonzero
    simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
      setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw,
      ownable_transferOwnership_sets_new_owner]
  · intro slotIdx h_slot
    have h_slot_raw : slotIdx ≠ 0 := by
      simpa [contractOwner] using h_slot
    by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_zero_raw : newOwner = 0
      · subst h_zero_raw
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, h_owner_raw, h_slot_raw,
          ownable_transferOwnership_keeps_other_owner_slots]
      · simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_zero_raw, h_slot_raw,
          ownable_transferOwnership_keeps_other_owner_slots]
    · simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw,
        ownable_transferOwnership_keeps_other_owner_slots]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_zero_raw : newOwner = 0
      · subst h_zero_raw
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, h_owner_raw, ownable_transferOwnership_keeps_uint_storage]
      · simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_zero_raw,
          ownable_transferOwnership_keeps_uint_storage]
    · simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw,
        ownable_transferOwnership_keeps_uint_storage]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_zero_raw : newOwner = 0
      · subst h_zero_raw
        refine ⟨?_, ?_, ?_⟩
        · funext slotIdx account
          simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
            setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.require, h_owner_raw]
        · funext slotIdx key
          simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
            setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.require, h_owner_raw]
        · funext slotIdx ownerAddr spender
          simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
            setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.require, h_owner_raw]
      · refine ⟨?_, ?_, ?_⟩
        · funext slotIdx account
          simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
            setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_zero_raw]
        · funext slotIdx key
          simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
            setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_zero_raw]
        · funext slotIdx ownerAddr spender
          simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
            setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_zero_raw]
    · refine ⟨?_, ?_, ?_⟩
      · funext slotIdx account
        simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
      · funext slotIdx key
        simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
      · funext slotIdx ownerAddr spender
        simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_zero_raw : newOwner = 0
      · subst h_zero_raw
        funext slotIdx
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, h_owner_raw]
      · funext slotIdx
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_zero_raw]
    · funext slotIdx
      simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]

-- tama: discharges=ownable_transferOwnership_reverts_for_non_owner
theorem transferOwnership_reverts_for_non_owner (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_reverts_for_non_owner newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).1

-- tama: discharges=ownable_transferOwnership_reverts_for_zero_owner
theorem transferOwnership_reverts_for_zero_owner (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_reverts_for_zero_owner newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.1

-- tama: discharges=ownable_transferOwnership_succeeds_for_owner_to_nonzero
theorem transferOwnership_succeeds_for_owner_to_nonzero (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_succeeds_for_owner_to_nonzero newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.2.1

-- tama: discharges=ownable_transferOwnership_sets_new_owner
theorem transferOwnership_sets_new_owner (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_sets_new_owner newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.2.2.1

-- tama: discharges=ownable_transferOwnership_keeps_other_owner_slots
theorem transferOwnership_keeps_other_owner_slots (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_keeps_other_owner_slots newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.2.2.2.1

-- tama: discharges=ownable_transferOwnership_keeps_uint_storage
theorem transferOwnership_keeps_uint_storage (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_keeps_uint_storage newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.2.2.2.2.1

-- tama: discharges=ownable_transferOwnership_keeps_balances_and_allowances
theorem transferOwnership_keeps_balances_and_allowances (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_keeps_balances_and_allowances newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.2.2.2.2.2.1

-- tama: discharges=ownable_transferOwnership_keeps_array_storage
theorem transferOwnership_keeps_array_storage (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_keeps_array_storage newOwner s
    ((transferOwnership newOwner).run s) :=
  (transferOwnership_properties_after_run newOwner s).2.2.2.2.2.2.2

private theorem renounceOwnership_properties_after_run (s : ContractState) :
  ownable_renounceOwnership_reverts_for_non_owner s ((renounceOwnership).run s) ∧
  ownable_renounceOwnership_succeeds_for_owner s ((renounceOwnership).run s) ∧
  ownable_renounceOwnership_clears_owner s ((renounceOwnership).run s) ∧
  ownable_renounceOwnership_keeps_other_owner_slots s ((renounceOwnership).run s) ∧
  ownable_renounceOwnership_keeps_uint_storage s ((renounceOwnership).run s) ∧
  ownable_renounceOwnership_keeps_balances_and_allowances s ((renounceOwnership).run s) ∧
  ownable_renounceOwnership_keeps_array_storage s ((renounceOwnership).run s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa [contractOwner] using h_not_owner
    simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_owner_raw,
      ownable_renounceOwnership_reverts_for_non_owner]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
      setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure, h_owner_raw,
      ownable_renounceOwnership_succeeds_for_owner]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
      setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure, h_owner_raw,
      ownable_renounceOwnership_clears_owner]
  · intro slotIdx h_slot
    have h_slot_raw : slotIdx ≠ 0 := by
      simpa [contractOwner] using h_slot
    by_cases h_owner_raw : s.sender = s.storageAddr 0
    · simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_slot_raw,
        ownable_renounceOwnership_keeps_other_owner_slots]
    · simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw,
        ownable_renounceOwnership_keeps_other_owner_slots]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw,
        ownable_renounceOwnership_keeps_uint_storage]
    · simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw,
        ownable_renounceOwnership_keeps_uint_storage]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · refine ⟨?_, ?_, ?_⟩
      · funext slotIdx account
        simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw]
      · funext slotIdx key
        simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw]
      · funext slotIdx ownerAddr spender
        simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw]
    · refine ⟨?_, ?_, ?_⟩
      · funext slotIdx account
        simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
      · funext slotIdx key
        simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
      · funext slotIdx ownerAddr spender
        simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · funext slotIdx
      simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw]
    · funext slotIdx
      simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_owner_raw]

-- tama: discharges=ownable_renounceOwnership_reverts_for_non_owner
theorem renounceOwnership_reverts_for_non_owner (s : ContractState) :
  ownable_renounceOwnership_reverts_for_non_owner s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).1

-- tama: discharges=ownable_renounceOwnership_succeeds_for_owner
theorem renounceOwnership_succeeds_for_owner (s : ContractState) :
  ownable_renounceOwnership_succeeds_for_owner s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).2.1

-- tama: discharges=ownable_renounceOwnership_clears_owner
theorem renounceOwnership_clears_owner (s : ContractState) :
  ownable_renounceOwnership_clears_owner s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).2.2.1

-- tama: discharges=ownable_renounceOwnership_keeps_other_owner_slots
theorem renounceOwnership_keeps_other_owner_slots (s : ContractState) :
  ownable_renounceOwnership_keeps_other_owner_slots s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).2.2.2.1

-- tama: discharges=ownable_renounceOwnership_keeps_uint_storage
theorem renounceOwnership_keeps_uint_storage (s : ContractState) :
  ownable_renounceOwnership_keeps_uint_storage s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).2.2.2.2.1

-- tama: discharges=ownable_renounceOwnership_keeps_balances_and_allowances
theorem renounceOwnership_keeps_balances_and_allowances (s : ContractState) :
  ownable_renounceOwnership_keeps_balances_and_allowances s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).2.2.2.2.2.1

-- tama: discharges=ownable_renounceOwnership_keeps_array_storage
theorem renounceOwnership_keeps_array_storage (s : ContractState) :
  ownable_renounceOwnership_keeps_array_storage s ((renounceOwnership).run s) :=
  (renounceOwnership_properties_after_run s).2.2.2.2.2.2

end Tamago.Proof.Auth.OwnableProof
