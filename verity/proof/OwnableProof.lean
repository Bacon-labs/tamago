import spec.OwnableSpec
import Verity.Proofs.Stdlib.Automation

namespace proof.OwnableProof

set_option linter.unusedSimpArgs false

open Verity
open spec.OwnableSpec
open src.Ownable

attribute [local simp] contractOwner

-- tama: discharges=ownable_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  ownable_owner_spec ((owner).run s).fst s := by
  simp [ownable_owner_spec, owner, contractOwner, Bind.bind, Pure.pure]

-- tama: discharges=ownable_transferOwnership_effect
theorem transferOwnership_effect_after_run (newOwner : Address) (s : ContractState) :
  ownable_transferOwnership_effect newOwner s ((transferOwnership newOwner).run s) := by
  unfold ownable_transferOwnership_effect
  refine ⟨?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa [contractOwner] using h_not_owner
    simp [transferOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_owner_raw]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    refine ⟨?_, ?_⟩
    · intro h_zero
      have h_zero_raw : newOwner = 0 := by
        simpa [zeroAddress] using h_zero
      subst h_zero_raw
      simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        Contract.run, Verity.bind, Bind.bind, Verity.require, h_owner_raw]
    · intro h_nonzero
      have h_nonzero_raw : newOwner ≠ 0 := by
        simpa [zeroAddress] using h_nonzero
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]
      · simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]
      · intro slotIdx h_slot
        have h_slot_raw : slotIdx ≠ 0 := by
          simpa [contractOwner] using h_slot
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw, h_slot_raw]
      · simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]
      · funext slotIdx account
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]
      · funext slotIdx key
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]
      · funext slotIdx ownerAddr spender
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]
      · funext slotIdx
        simp [transferOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
          setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_nonzero_raw]

-- tama: discharges=ownable_renounceOwnership_effect
theorem renounceOwnership_effect_after_run (s : ContractState) :
  ownable_renounceOwnership_effect s ((renounceOwnership).run s) := by
  unfold ownable_renounceOwnership_effect
  refine ⟨?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa [contractOwner] using h_not_owner
    simp [renounceOwnership, contractOwner, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_owner_raw]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa [contractOwner] using h_owner
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw]
    · simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw]
    · intro slotIdx h_slot
      have h_slot_raw : slotIdx ≠ 0 := by
        simpa [contractOwner] using h_slot
      simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw, h_slot_raw]
    · simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw]
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
    · funext slotIdx
      simp [renounceOwnership, contractOwner, zeroAddress, msgSender, getStorageAddr,
        setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, Verity.pure, Pure.pure, h_owner_raw]

end proof.OwnableProof
