import spec.ERC721Spec
import Verity.Proofs.Stdlib.Automation

namespace proof.ERC721Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open spec.ERC721Spec
open src.ERC721

-- tama: discharges=erc721_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc721_totalSupply_spec ((totalSupply).run s).fst s := by
  simp [erc721_totalSupply_spec, totalSupply, totalSupplySlot, Bind.bind, Pure.pure]

-- tama: discharges=erc721_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  erc721_owner_spec ((owner).run s).fst s := by
  simp [erc721_owner_spec, owner, ownerSlot, Bind.bind, Pure.pure]

-- tama: discharges=erc721_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc721_balanceOf_spec account ((balanceOf account).run s).fst s := by
  unfold erc721_balanceOf_spec
  intro h_nonzero
  have h_zero : ¬ account = 0 := by
    simpa [zeroAddress] using h_nonzero
  simp [balanceOf, balancesSlot, getMapping, Verity.require, Contract.run, ContractResult.fst,
    h_zero, Bind.bind, Pure.pure, Verity.bind, Verity.pure]

-- tama: discharges=erc721_ownerOf_spec
theorem ownerOf_matches_storage_or_reverts (tokenId : Uint256) (s : ContractState) :
  erc721_ownerOf_spec tokenId ((ownerOf tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [erc721_ownerOf_spec, ownerOf, ownersSlot, getMappingUint, Contract.run,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_owner]

-- tama: discharges=erc721_getApproved_spec
theorem getApproved_matches_storage_or_reverts (tokenId : Uint256) (s : ContractState) :
  erc721_getApproved_spec tokenId ((getApproved tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [erc721_getApproved_spec, getApproved, ownersSlot, tokenApprovalsSlot,
      getMappingUint, getMappingUintAddr, Contract.run, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure, h_owner]

-- tama: discharges=erc721_isApprovedForAll_spec
theorem isApprovedForAll_matches_storage (ownerAddr operator : Address) (s : ContractState) :
  erc721_isApprovedForAll_spec ownerAddr operator ((isApprovedForAll ownerAddr operator).run s).fst s := by
  simp [erc721_isApprovedForAll_spec, isApprovedForAll, operatorApprovalsSlot, getMapping2,
    Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]

-- tama: discharges=erc721_setApprovalForAll_effect
theorem setApprovalForAll_updates_operator_slot
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_effect operator approved s ((setApprovalForAll operator approved).run s).snd := by
  unfold erc721_setApprovalForAll_effect
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases approved <;>
      simp [setApprovalForAll, operatorApprovalsSlot, src.boolToWord, msgSender,
        setMapping2, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure]
  · simp [setApprovalForAll, operatorApprovalsSlot, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [setApprovalForAll, operatorApprovalsSlot, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx key
    simp [setApprovalForAll, operatorApprovalsSlot, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=erc721_approve_effect
theorem approve_updates_token_approval_when_authorized
    (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_effect approved tokenId s ((approve approved tokenId).run s).snd := by
  unfold erc721_approve_effect
  intro h_exists h_authorized
  have h_authorized_prop :
      s.sender = wordToAddress (s.storageMapUint 4 tokenId) ∨
        ¬ s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender = 0 := by
    simpa [Bool.or_eq_true, beq_iff_eq] using h_authorized
  rcases h_authorized_prop with h_sender | h_operator
  · simp [approve, ownersSlot, tokenApprovalsSlot, operatorApprovalsSlot, getMappingUint,
      getMapping2, setMappingUintAddr, setMappingUint, msgSender, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_exists,
      h_sender, wordToAddress, addressToWord]
  · have h_operator' :
        ¬s.storageMap2 6 (Core.Address.ofNat (s.storageMapUint 4 tokenId).val) s.sender = 0 := by
      simpa [wordToAddress] using h_operator
    simp [approve, ownersSlot, tokenApprovalsSlot, operatorApprovalsSlot, getMappingUint,
      getMapping2, setMappingUintAddr, setMappingUint, msgSender, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_exists,
      h_operator', wordToAddress, addressToWord]

-- tama: discharges=erc721_mint_effect
theorem mint_updates_owner_balance_supply_and_counter
    (toAddr : Address) (s : ContractState) :
  erc721_mint_effect toAddr s ((mint toAddr).run s).snd ((mint toAddr).run s).fst := by
  unfold erc721_mint_effect
  intro h_owner h_recipient h_unminted h_balance_no_overflow h_supply_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + 1 := by omega
  have h_recipient_zero : ¬ toAddr = 0 := by
    simpa [zeroAddress] using h_recipient
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, nextTokenIdSlot, ownersSlot,
      msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, setMappingUintAddr,
      setMappingUint, setMapping, setStorage, Contract.run, ContractResult.fst, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_recipient, h_unminted,
      h_recipient_zero, h_not_balance_overflow, h_not_supply_overflow, Verity.pure, Pure.pure]
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, nextTokenIdSlot, ownersSlot,
      msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, setMappingUintAddr,
      setMappingUint, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_recipient, h_unminted,
      h_recipient_zero, h_not_balance_overflow, h_not_supply_overflow, Verity.pure, Pure.pure]
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, nextTokenIdSlot, ownersSlot,
      msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, setMappingUintAddr,
      setMappingUint, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_recipient, h_unminted,
      h_recipient_zero, h_not_balance_overflow, h_not_supply_overflow, Verity.pure, Pure.pure]
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, nextTokenIdSlot, ownersSlot,
      msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, setMappingUintAddr,
      setMappingUint, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_recipient, h_unminted,
      h_recipient_zero, h_not_balance_overflow, h_not_supply_overflow,
      Verity.pure, Pure.pure]
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, nextTokenIdSlot, ownersSlot,
      msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, setMappingUintAddr,
      setMappingUint, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_recipient, h_unminted,
      h_recipient_zero, h_not_balance_overflow, h_not_supply_overflow, Verity.pure, Pure.pure]

-- tama: discharges=erc721_mint_unauthorized_no_change
theorem mint_unauthorized_no_change_after_run (toAddr : Address) (s : ContractState) :
  erc721_mint_unauthorized_no_change toAddr s ((mint toAddr).run s).snd := by
  unfold erc721_mint_unauthorized_no_change
  intro h_not_owner
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mint, ownerSlot, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_not_owner]

-- tama: discharges=erc721_transferFrom_zero_recipient_no_change
theorem transferFrom_zero_recipient_reverts_without_storage_change
    (fromAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_zero_recipient_no_change fromAddr tokenId s
    ((transferFrom fromAddr zeroAddress tokenId).run s).snd := by
  unfold erc721_transferFrom_zero_recipient_no_change
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [transferFrom, msgSender, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require]

end proof.ERC721Proof
