import Tamago.Spec.Tokens.ERC721Spec
import Tamago.Proof.Auth.OwnableProof
import Tamago.Proof.EventSimp
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Tokens.ERC721Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Tamago.Spec.Tokens.ERC721Spec
open Tamago.Tokens.ERC721

attribute [local simp] contractOwner tokenSupply nextTokenId balances tokenOwners tokenApprovals operatorApprovals
  Tamago.Tokens.ERC721Base.contractOwner Tamago.Tokens.ERC721Base.tokenSupply Tamago.Tokens.ERC721Base.nextTokenId
  Tamago.Tokens.ERC721Base.balances Tamago.Tokens.ERC721Base.tokenOwners Tamago.Tokens.ERC721Base.tokenApprovals
  Tamago.Tokens.ERC721Base.operatorApprovals Tamago.Tokens.ERC721Base.totalSupply Tamago.Tokens.ERC721Base.owner
  Tamago.Tokens.ERC721Base.transferOwnership Tamago.Tokens.ERC721Base.renounceOwnership
  Tamago.Tokens.ERC721Base.balanceOf Tamago.Tokens.ERC721Base.ownerOf Tamago.Tokens.ERC721Base.getApproved
  Tamago.Tokens.ERC721Base.isApprovedForAll Tamago.Tokens.ERC721Base.approve
  Tamago.Tokens.ERC721Base.setApprovalForAll Tamago.Tokens.ERC721Base.mint Tamago.Tokens.ERC721Base.transferFrom
  Tamago.Auth.OwnableBase.contractOwner Tamago.Auth.OwnableBase.transferOwnership
  Tamago.Auth.OwnableBase.renounceOwnership Contracts.emit emitEvent

-- tama: discharges=erc721_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc721_totalSupply_spec ((totalSupply).run s).fst s := by
  simp [erc721_totalSupply_spec, totalSupply, tokenSupply, Bind.bind, Pure.pure]

-- tama: discharges=erc721_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  erc721_owner_spec ((owner).run s).fst s := by
  simp [erc721_owner_spec, Tamago.Spec.Auth.OwnableSpec.ownable_owner_spec, owner, contractOwner,
    Tamago.Auth.Ownable.contractOwner, Bind.bind, Pure.pure]

-- tama: discharges=erc721_transferOwnership_reverts_for_non_owner
theorem transferOwnership_reverts_for_non_owner (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_reverts_for_non_owner newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_reverts_for_non_owner,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_reverts_for_non_owner newOwner s

-- tama: discharges=erc721_transferOwnership_reverts_for_zero_owner
theorem transferOwnership_reverts_for_zero_owner (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_reverts_for_zero_owner newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_reverts_for_zero_owner,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_reverts_for_zero_owner newOwner s

-- tama: discharges=erc721_transferOwnership_succeeds_for_owner_to_nonzero
theorem transferOwnership_succeeds_for_owner_to_nonzero (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_succeeds_for_owner_to_nonzero newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_succeeds_for_owner_to_nonzero,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_succeeds_for_owner_to_nonzero newOwner s

-- tama: discharges=erc721_transferOwnership_sets_new_owner
theorem transferOwnership_sets_new_owner (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_sets_new_owner newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_sets_new_owner,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_sets_new_owner newOwner s

-- tama: discharges=erc721_transferOwnership_keeps_other_owner_slots
theorem transferOwnership_keeps_other_owner_slots (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_keeps_other_owner_slots newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_keeps_other_owner_slots,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_other_owner_slots newOwner s

-- tama: discharges=erc721_transferOwnership_keeps_uint_storage
theorem transferOwnership_keeps_uint_storage (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_keeps_uint_storage newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_keeps_uint_storage,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_uint_storage newOwner s

-- tama: discharges=erc721_transferOwnership_keeps_balances_and_allowances
theorem transferOwnership_keeps_balances_and_allowances (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_keeps_balances_and_allowances newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_keeps_balances_and_allowances,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_balances_and_allowances newOwner s

-- tama: discharges=erc721_transferOwnership_keeps_array_storage
theorem transferOwnership_keeps_array_storage (newOwner : Address) (s : ContractState) :
  erc721_transferOwnership_keeps_array_storage newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc721_transferOwnership_keeps_array_storage,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_array_storage newOwner s

-- tama: discharges=erc721_renounceOwnership_reverts_for_non_owner
theorem renounceOwnership_reverts_for_non_owner (s : ContractState) :
  erc721_renounceOwnership_reverts_for_non_owner s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_reverts_for_non_owner,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_reverts_for_non_owner s

-- tama: discharges=erc721_renounceOwnership_succeeds_for_owner
theorem renounceOwnership_succeeds_for_owner (s : ContractState) :
  erc721_renounceOwnership_succeeds_for_owner s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_succeeds_for_owner,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_succeeds_for_owner s

-- tama: discharges=erc721_renounceOwnership_clears_owner
theorem renounceOwnership_clears_owner (s : ContractState) :
  erc721_renounceOwnership_clears_owner s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_clears_owner,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_clears_owner s

-- tama: discharges=erc721_renounceOwnership_keeps_other_owner_slots
theorem renounceOwnership_keeps_other_owner_slots (s : ContractState) :
  erc721_renounceOwnership_keeps_other_owner_slots s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_keeps_other_owner_slots,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_other_owner_slots s

-- tama: discharges=erc721_renounceOwnership_keeps_uint_storage
theorem renounceOwnership_keeps_uint_storage (s : ContractState) :
  erc721_renounceOwnership_keeps_uint_storage s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_keeps_uint_storage,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_uint_storage s

-- tama: discharges=erc721_renounceOwnership_keeps_balances_and_allowances
theorem renounceOwnership_keeps_balances_and_allowances (s : ContractState) :
  erc721_renounceOwnership_keeps_balances_and_allowances s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_keeps_balances_and_allowances,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_balances_and_allowances s

-- tama: discharges=erc721_renounceOwnership_keeps_array_storage
theorem renounceOwnership_keeps_array_storage (s : ContractState) :
  erc721_renounceOwnership_keeps_array_storage s ((renounceOwnership).run s) := by
  simpa [erc721_renounceOwnership_keeps_array_storage,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_array_storage s

-- tama: discharges=erc721_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc721_balanceOf_spec account ((balanceOf account).run s) s := by
  unfold erc721_balanceOf_spec
  refine ⟨?_, ?_⟩
  · intro h_zero
    subst h_zero
    simp [balanceOf, zeroAddress, getMapping, Verity.require, Contract.run,
      Bind.bind, Pure.pure, Verity.bind, Verity.pure]
  · intro h_nonzero
    have h_nonzero_raw : ¬ account = 0 := by
      simpa [zeroAddress] using h_nonzero
    simp [balanceOf, zeroAddress, getMapping, Verity.require, Contract.run,
      h_nonzero_raw, Bind.bind, Pure.pure, Verity.bind, Verity.pure]

-- tama: discharges=erc721_ownerOf_spec
theorem ownerOf_matches_storage_or_reverts (tokenId : Uint256) (s : ContractState) :
  erc721_ownerOf_spec tokenId ((ownerOf tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [erc721_ownerOf_spec, ownerOf, tokenOwners, getMappingUint, Contract.run,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_owner]

-- tama: discharges=erc721_getApproved_spec
theorem getApproved_matches_storage_or_reverts (tokenId : Uint256) (s : ContractState) :
  erc721_getApproved_spec tokenId ((getApproved tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [erc721_getApproved_spec, getApproved, tokenOwners, tokenApprovals,
      getMappingUint, getMappingUintAddr, Contract.run, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure, h_owner]

-- tama: discharges=erc721_isApprovedForAll_spec
theorem isApprovedForAll_matches_storage (ownerAddr operator : Address) (s : ContractState) :
  erc721_isApprovedForAll_spec ownerAddr operator ((isApprovedForAll ownerAddr operator).run s).fst s := by
  simp [erc721_isApprovedForAll_spec, isApprovedForAll, operatorApprovals, getMapping2,
    Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]

private theorem setApprovalForAll_properties_after_run
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_succeeds operator approved s ((setApprovalForAll operator approved).run s) ∧
  erc721_setApprovalForAll_sets_operator_flag operator approved s ((setApprovalForAll operator approved).run s) ∧
  erc721_setApprovalForAll_keeps_supply operator approved s ((setApprovalForAll operator approved).run s) ∧
  erc721_setApprovalForAll_keeps_balances_and_owners operator approved s
    ((setApprovalForAll operator approved).run s) := by
  unfold erc721_setApprovalForAll_succeeds
    erc721_setApprovalForAll_sets_operator_flag erc721_setApprovalForAll_keeps_supply
    erc721_setApprovalForAll_keeps_balances_and_owners
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases approved <;>
      simp [setApprovalForAll, operatorApprovals, Tamago.Tokens.boolToWord, msgSender,
        setMapping2, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure]
  · simp [setApprovalForAll, operatorApprovals, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [setApprovalForAll, operatorApprovals, tokenSupply, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · refine ⟨?_, ?_⟩
    · funext slotIdx addr
      simp [setApprovalForAll, operatorApprovals, msgSender, setMapping2,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
    · funext slotIdx key
      simp [setApprovalForAll, operatorApprovals, msgSender, setMapping2,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=erc721_setApprovalForAll_succeeds
theorem setApprovalForAll_succeeds
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_succeeds operator approved s
    ((setApprovalForAll operator approved).run s) := by
  rcases setApprovalForAll_properties_after_run operator approved s with
    ⟨h_succeeds, _h_sets, _h_supply, _h_balances⟩
  exact h_succeeds

-- tama: discharges=erc721_setApprovalForAll_sets_operator_flag
theorem setApprovalForAll_sets_operator_flag
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_sets_operator_flag operator approved s
    ((setApprovalForAll operator approved).run s) := by
  rcases setApprovalForAll_properties_after_run operator approved s with
    ⟨_h_succeeds, h_sets, _h_supply, _h_balances⟩
  exact h_sets

-- tama: discharges=erc721_setApprovalForAll_keeps_supply
theorem setApprovalForAll_keeps_supply
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_keeps_supply operator approved s
    ((setApprovalForAll operator approved).run s) := by
  rcases setApprovalForAll_properties_after_run operator approved s with
    ⟨_h_succeeds, _h_sets, h_supply, _h_balances⟩
  exact h_supply

-- tama: discharges=erc721_setApprovalForAll_keeps_balances_and_owners
theorem setApprovalForAll_keeps_balances_and_owners
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_keeps_balances_and_owners operator approved s
    ((setApprovalForAll operator approved).run s) := by
  rcases setApprovalForAll_properties_after_run operator approved s with
    ⟨_h_succeeds, _h_sets, _h_supply, h_balances⟩
  exact h_balances

  private theorem approve_properties_after_run
      (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_reverts_when_token_is_missing approved tokenId s ((approve approved tokenId).run s) ∧
  erc721_approve_reverts_when_sender_is_not_authorized approved tokenId s ((approve approved tokenId).run s) ∧
  erc721_approve_succeeds_when_sender_is_authorized approved tokenId s ((approve approved tokenId).run s) ∧
  erc721_approve_sets_token_approval approved tokenId s ((approve approved tokenId).run s) := by
  unfold erc721_approve_reverts_when_token_is_missing
    erc721_approve_reverts_when_sender_is_not_authorized
    erc721_approve_succeeds_when_sender_is_authorized erc721_approve_sets_token_approval
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h_missing
    have h_missing_raw : s.storageMapUint 4 tokenId = 0 := by
      simpa using h_missing
    simp [approve, tokenOwners, tokenApprovals, operatorApprovals, getMappingUint,
      getMapping2, setMappingUintAddr, msgSender, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_missing_raw]
  · intro h_exists h_unauthorized
    have h_exists_raw : (s.storageMapUint 4 tokenId != 0) = true := by
      simpa using h_exists
    have h_unauthorized_raw :
        ((s.sender == wordToAddress (s.storageMapUint 4 tokenId)) ||
          (s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender != 0)) =
            false := by
      simpa using h_unauthorized
    have h_unauthorized_prop :
        ¬ (s.sender = wordToAddress (s.storageMapUint 4 tokenId) ∨
          ¬ s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender = 0) := by
      simpa [Bool.or_eq_true, beq_iff_eq] using h_unauthorized_raw
    have h_unauthorized_prop_raw :
        ¬ (s.sender = Core.Address.ofNat (s.storageMapUint 4 tokenId).val ∨
          ¬ s.storageMap2 6 (Core.Address.ofNat (s.storageMapUint 4 tokenId).val) s.sender = 0) := by
      simpa [wordToAddress] using h_unauthorized_prop
    simp [approve, tokenOwners, tokenApprovals, operatorApprovals, getMappingUint,
      getMapping2, setMappingUintAddr, msgSender, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_exists_raw,
      h_unauthorized_prop_raw, wordToAddress]
  · intro h_exists h_authorized
    have h_exists_raw : (s.storageMapUint 4 tokenId != 0) = true := by
      simpa using h_exists
    have h_authorized_raw :
        ((s.sender == wordToAddress (s.storageMapUint 4 tokenId)) ||
          (s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender != 0)) =
            true := by
      simpa using h_authorized
    have h_authorized_prop :
        s.sender = wordToAddress (s.storageMapUint 4 tokenId) ∨
          ¬ s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender = 0 := by
      simpa [Bool.or_eq_true, beq_iff_eq] using h_authorized_raw
    have h_authorized_prop_raw :
        s.sender = Core.Address.ofNat (s.storageMapUint 4 tokenId).val ∨
          ¬ s.storageMap2 6 (Core.Address.ofNat (s.storageMapUint 4 tokenId).val) s.sender = 0 := by
      simpa [wordToAddress] using h_authorized_prop
    simp [approve, tokenOwners, tokenApprovals, operatorApprovals, getMappingUint,
      getMapping2, setMappingUintAddr, setMappingUint, msgSender, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
      h_exists_raw, h_authorized_prop_raw, wordToAddress, addressToWord]
  · intro h_exists h_authorized
    have h_exists_raw : (s.storageMapUint 4 tokenId != 0) = true := by
      simpa using h_exists
    have h_authorized_raw :
        ((s.sender == wordToAddress (s.storageMapUint 4 tokenId)) ||
          (s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender != 0)) =
            true := by
      simpa using h_authorized
    have h_authorized_prop :
        s.sender = wordToAddress (s.storageMapUint 4 tokenId) ∨
          ¬ s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender = 0 := by
      simpa [Bool.or_eq_true, beq_iff_eq] using h_authorized_raw
    have h_authorized_prop_raw :
        s.sender = Core.Address.ofNat (s.storageMapUint 4 tokenId).val ∨
          ¬ s.storageMap2 6 (Core.Address.ofNat (s.storageMapUint 4 tokenId).val) s.sender = 0 := by
      simpa [wordToAddress] using h_authorized_prop
    simp [approve, tokenOwners, tokenApprovals, operatorApprovals, getMappingUint,
      getMapping2, setMappingUintAddr, setMappingUint, msgSender, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
      h_exists_raw, h_authorized_prop_raw, wordToAddress, addressToWord]

-- tama: discharges=erc721_approve_reverts_when_token_is_missing
theorem approve_reverts_when_token_is_missing
    (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_reverts_when_token_is_missing approved tokenId s
    ((approve approved tokenId).run s) := by
  rcases approve_properties_after_run approved tokenId s with
    ⟨h_missing, _h_unauthorized, _h_succeeds, _h_sets⟩
  exact h_missing

-- tama: discharges=erc721_approve_reverts_when_sender_is_not_authorized
theorem approve_reverts_when_sender_is_not_authorized
    (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_reverts_when_sender_is_not_authorized approved tokenId s
    ((approve approved tokenId).run s) := by
  rcases approve_properties_after_run approved tokenId s with
    ⟨_h_missing, h_unauthorized, _h_succeeds, _h_sets⟩
  exact h_unauthorized

-- tama: discharges=erc721_approve_succeeds_when_sender_is_authorized
theorem approve_succeeds_when_sender_is_authorized
    (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_succeeds_when_sender_is_authorized approved tokenId s
    ((approve approved tokenId).run s) := by
  rcases approve_properties_after_run approved tokenId s with
    ⟨_h_missing, _h_unauthorized, h_succeeds, _h_sets⟩
  exact h_succeeds

-- tama: discharges=erc721_approve_sets_token_approval
theorem approve_sets_token_approval
    (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_sets_token_approval approved tokenId s ((approve approved tokenId).run s) := by
  rcases approve_properties_after_run approved tokenId s with
    ⟨_h_missing, _h_unauthorized, _h_succeeds, h_sets⟩
  exact h_sets

private theorem mint_properties_after_run
    (toAddr : Address) (s : ContractState) :
  erc721_mint_reverts_for_non_owner toAddr s ((mint toAddr).run s) ∧
  erc721_mint_reverts_for_zero_recipient toAddr s ((mint toAddr).run s) ∧
  erc721_mint_reverts_when_next_token_is_already_minted toAddr s ((mint toAddr).run s) ∧
  erc721_mint_reverts_when_recipient_balance_would_overflow toAddr s ((mint toAddr).run s) ∧
  erc721_mint_reverts_when_total_supply_would_overflow toAddr s ((mint toAddr).run s) ∧
  erc721_mint_succeeds_with_next_token_id toAddr s ((mint toAddr).run s) ∧
  erc721_mint_assigns_next_token_to_recipient toAddr s ((mint toAddr).run s) ∧
  erc721_mint_credits_recipient_balance toAddr s ((mint toAddr).run s) ∧
  erc721_mint_increases_total_supply toAddr s ((mint toAddr).run s) ∧
  erc721_mint_advances_next_token_id toAddr s ((mint toAddr).run s) := by
  unfold erc721_mint_reverts_for_non_owner
    erc721_mint_reverts_for_zero_recipient
    erc721_mint_reverts_when_next_token_is_already_minted
    erc721_mint_reverts_when_recipient_balance_would_overflow
    erc721_mint_reverts_when_total_supply_would_overflow
    erc721_mint_succeeds_with_next_token_id erc721_mint_assigns_next_token_to_recipient
    erc721_mint_credits_recipient_balance erc721_mint_increases_total_supply
    erc721_mint_advances_next_token_id
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa using h_not_owner
    simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_owner_raw]
  · intro h_owner h_zero
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_zero_raw : toAddr = 0 := by
      simpa [zeroAddress] using h_zero
    subst h_zero_raw
    simp [mint, contractOwner, zeroAddress, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_owner_raw]
  · intro h_owner h_recipient h_minted
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_recipient_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_recipient
    have h_minted_raw : s.storageMapUint 4 (s.storage 2) ≠ 0 := by
      simpa using h_minted
    simp [mint, contractOwner, zeroAddress, nextTokenId, tokenOwners, msgSender,
      getStorageAddr, getStorage, getMappingUint, Contract.run, Verity.bind,
      Bind.bind, Verity.require, h_owner_raw, h_recipient_raw, h_minted_raw]
  · intro h_owner h_recipient h_unminted h_balance_overflow
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_recipient_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_recipient
    have h_unminted_raw : s.storageMapUint 4 (s.storage 2) = 0 := by
      simpa using h_unminted
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by
      simpa using h_balance_overflow
    simp [mint, contractOwner, zeroAddress, balances, nextTokenId, tokenOwners,
      msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, Contract.run,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner_raw, h_recipient_raw, h_unminted_raw,
      h_overflow]
  · intro h_owner h_recipient h_unminted h_balance_no_overflow h_supply_overflow
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_recipient_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_recipient
    have h_unminted_raw : s.storageMapUint 4 (s.storage 2) = 0 := by
      simpa using h_unminted
    have h_balance_no_overflow_raw :
        (s.storageMap 3 toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    have h_not_balance_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by
      omega
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + 1 := by
      simpa using h_supply_overflow
    simp [mint, contractOwner, zeroAddress, balances, tokenSupply, nextTokenId,
      tokenOwners, msgSender, getStorageAddr, getStorage, getMappingUint, getMapping,
      Contract.run, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw,
      h_recipient_raw, h_unminted_raw, h_not_balance_overflow, h_overflow,
      Verity.pure, Pure.pure]
  all_goals
      intro h_owner h_recipient h_unminted h_balance_no_overflow h_supply_no_overflow
      have h_owner_raw : s.sender = s.storageAddr 0 := by
        simpa using h_owner
      have h_recipient_raw : ¬ toAddr = 0 := by
        simpa [zeroAddress] using h_recipient
      have h_unminted_raw : s.storageMapUint 4 (s.storage 2) = 0 := by
        simpa using h_unminted
      have h_balance_no_overflow_raw :
          (s.storageMap 3 toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_balance_no_overflow
      have h_not_balance_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by
        omega
      have h_supply_no_overflow_raw :
          (s.storage 1).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_supply_no_overflow
      have h_not_supply_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + 1 := by
        omega
      simp [mint, contractOwner, zeroAddress, balances, tokenSupply, nextTokenId,
        tokenOwners, msgSender, getStorageAddr, getStorage, getMappingUint, getMapping,
        setMappingUintAddr, setMappingUint, setMapping, setStorage, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw,
        h_recipient_raw, h_unminted_raw, h_not_balance_overflow,
        h_not_supply_overflow, Verity.pure, Pure.pure]

-- tama: discharges=erc721_mint_reverts_for_non_owner
theorem mint_reverts_for_non_owner (toAddr : Address) (s : ContractState) :
  erc721_mint_reverts_for_non_owner toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨h_non_owner, _h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_non_owner

-- tama: discharges=erc721_mint_reverts_for_zero_recipient
theorem mint_reverts_for_zero_recipient (toAddr : Address) (s : ContractState) :
  erc721_mint_reverts_for_zero_recipient toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_zero

-- tama: discharges=erc721_mint_reverts_when_next_token_is_already_minted
theorem mint_reverts_when_next_token_is_already_minted (toAddr : Address) (s : ContractState) :
  erc721_mint_reverts_when_next_token_is_already_minted toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_minted

-- tama: discharges=erc721_mint_reverts_when_recipient_balance_would_overflow
theorem mint_reverts_when_recipient_balance_would_overflow (toAddr : Address) (s : ContractState) :
  erc721_mint_reverts_when_recipient_balance_would_overflow toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_balance_overflow

-- tama: discharges=erc721_mint_reverts_when_total_supply_would_overflow
theorem mint_reverts_when_total_supply_would_overflow (toAddr : Address) (s : ContractState) :
  erc721_mint_reverts_when_total_supply_would_overflow toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, _h_balance_overflow, h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_supply_overflow

-- tama: discharges=erc721_mint_succeeds_with_next_token_id
theorem mint_succeeds_with_next_token_id (toAddr : Address) (s : ContractState) :
  erc721_mint_succeeds_with_next_token_id toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      h_succeeds, _h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_succeeds

-- tama: discharges=erc721_mint_assigns_next_token_to_recipient
theorem mint_assigns_next_token_to_recipient (toAddr : Address) (s : ContractState) :
  erc721_mint_assigns_next_token_to_recipient toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, h_assigns, _h_credits, _h_supply, _h_counter⟩
  exact h_assigns

-- tama: discharges=erc721_mint_credits_recipient_balance
theorem mint_credits_recipient_balance (toAddr : Address) (s : ContractState) :
  erc721_mint_credits_recipient_balance toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, h_credits, _h_supply, _h_counter⟩
  exact h_credits

-- tama: discharges=erc721_mint_increases_total_supply
theorem mint_increases_total_supply (toAddr : Address) (s : ContractState) :
  erc721_mint_increases_total_supply toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, h_supply, _h_counter⟩
  exact h_supply

-- tama: discharges=erc721_mint_advances_next_token_id
theorem mint_advances_next_token_id (toAddr : Address) (s : ContractState) :
  erc721_mint_advances_next_token_id toAddr s ((mint toAddr).run s) := by
  rcases mint_properties_after_run toAddr s with
    ⟨_h_non_owner, _h_zero, _h_minted, _h_balance_overflow, _h_supply_overflow,
      _h_succeeds, _h_assigns, _h_credits, _h_supply, h_counter⟩
  exact h_counter

private theorem transferFrom_properties_after_run
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_for_zero_recipient fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_reverts_when_token_is_missing fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_reverts_when_from_is_not_owner fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_reverts_when_sender_is_not_authorized fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_to_self_succeeds fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_to_self_keeps_balances fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_sets_owner_on_self_transfer fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_clears_approval_on_self_transfer fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_reverts_when_from_balance_is_low fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_reverts_when_to_balance_would_overflow fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_between_distinct_accounts_succeeds fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_sets_new_owner fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_clears_token_approval fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_debits_from_balance fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) ∧
  erc721_transferFrom_credits_to_balance fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  unfold erc721_transferFrom_reverts_for_zero_recipient
    erc721_transferFrom_reverts_when_token_is_missing
    erc721_transferFrom_reverts_when_from_is_not_owner
    erc721_transferFrom_reverts_when_sender_is_not_authorized
    erc721_transferFrom_to_self_succeeds erc721_transferFrom_to_self_keeps_balances
    erc721_transferFrom_sets_owner_on_self_transfer
    erc721_transferFrom_clears_approval_on_self_transfer
    erc721_transferFrom_reverts_when_from_balance_is_low
    erc721_transferFrom_reverts_when_to_balance_would_overflow
    erc721_transferFrom_between_distinct_accounts_succeeds
    erc721_transferFrom_sets_new_owner erc721_transferFrom_clears_token_approval
    erc721_transferFrom_debits_from_balance erc721_transferFrom_credits_to_balance
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_zero
    have h_zero_raw : toAddr = 0 := by
      simpa [zeroAddress] using h_zero
    subst h_zero_raw
    simp [transferFrom, zeroAddress, msgSender, Contract.run, Verity.bind, Bind.bind,
      Verity.require]
  · intro h_to_nonzero h_missing
    have h_to_nonzero_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_to_nonzero
    have h_missing_raw : s.storageMapUint 4 tokenId = 0 := by
      simpa using h_missing
    simp [transferFrom, zeroAddress, tokenOwners, msgSender, getMappingUint, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_to_nonzero_raw, h_missing_raw]
  · intro h_to_nonzero h_exists h_wrong_owner
    have h_to_nonzero_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_to_nonzero
    have h_exists_raw : s.storageMapUint 4 tokenId ≠ 0 := by
      simpa using h_exists
    have h_wrong_owner_raw :
        s.storageMapUint 4 tokenId ≠ addressToWord fromAddr := by
      simpa using h_wrong_owner
    have h_wrong_owner_raw' :
        s.storageMapUint 4 tokenId ≠ Core.Uint256.ofNat (Core.Address.toNat fromAddr) := by
      simpa [addressToWord] using h_wrong_owner_raw
    simp [transferFrom, zeroAddress, tokenOwners, msgSender, getMappingUint, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_to_nonzero_raw, h_exists_raw,
      h_wrong_owner_raw', addressToWord]
  · intro h_to_nonzero h_exists h_owner h_not_authorized
    have h_to_nonzero_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_to_nonzero
    have h_exists_raw : s.storageMapUint 4 tokenId ≠ 0 := by
      simpa using h_exists
    have h_owner_raw : s.storageMapUint 4 tokenId = addressToWord fromAddr := by
      simpa using h_owner
    have h_from_word_nonzero : addressToWord fromAddr ≠ 0 := by
      rw [← h_owner_raw]
      exact h_exists_raw
    have h_from_word_nonzero_raw :
        Core.Uint256.ofNat (Core.Address.toNat fromAddr) ≠ 0 := by
      simpa [addressToWord] using h_from_word_nonzero
    have h_not_authorized_raw :
        (((s.sender == fromAddr) ||
            (s.storageMapUint 5 tokenId == addressToWord s.sender)) ||
          (s.storageMap2 6 fromAddr s.sender != 0)) = false := by
      simpa using h_not_authorized
    have h_not_authorized_prop :
        ¬ ((s.sender = fromAddr ∨
              s.storageMapUint 5 tokenId = addressToWord s.sender) ∨
            ¬ s.storageMap2 6 fromAddr s.sender = 0) := by
      simpa [Bool.or_eq_true, beq_iff_eq] using h_not_authorized_raw
    have h_not_authorized_prop_raw :
        ¬ ((s.sender = fromAddr ∨
              s.storageMapUint 5 tokenId =
                Core.Uint256.ofNat (Core.Address.toNat s.sender)) ∨
            ¬ s.storageMap2 6 fromAddr s.sender = 0) := by
      simpa [addressToWord] using h_not_authorized_prop
    simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
      msgSender, getMappingUint, getMappingUintAddr, getMapping2, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_to_nonzero_raw, h_exists_raw,
      h_owner_raw, h_from_word_nonzero_raw, h_not_authorized_prop_raw, addressToWord]
  all_goals
      intro h_to_nonzero h_exists h_owner h_authorized
      have h_to_nonzero_raw : ¬ toAddr = 0 := by
        simpa [zeroAddress] using h_to_nonzero
      have h_exists_raw : s.storageMapUint 4 tokenId ≠ 0 := by
        simpa using h_exists
      have h_owner_raw : s.storageMapUint 4 tokenId = addressToWord fromAddr := by
        simpa using h_owner
      have h_from_word_nonzero : addressToWord fromAddr ≠ 0 := by
        rw [← h_owner_raw]
        exact h_exists_raw
      have h_from_word_nonzero_raw :
          Core.Uint256.ofNat (Core.Address.toNat fromAddr) ≠ 0 := by
        simpa [addressToWord] using h_from_word_nonzero
      have h_authorized_raw :
          (((s.sender == fromAddr) ||
              (s.storageMapUint 5 tokenId == addressToWord s.sender)) ||
            (s.storageMap2 6 fromAddr s.sender != 0)) = true := by
        simpa using h_authorized
      have h_authorized_prop :
          (s.sender = fromAddr ∨
              s.storageMapUint 5 tokenId = addressToWord s.sender) ∨
            ¬ s.storageMap2 6 fromAddr s.sender = 0 := by
        simpa [Bool.or_eq_true, beq_iff_eq] using h_authorized_raw
      have h_authorized_prop_raw :
          (s.sender = fromAddr ∨
              s.storageMapUint 5 tokenId =
                Core.Uint256.ofNat (Core.Address.toNat s.sender)) ∨
            ¬ s.storageMap2 6 fromAddr s.sender = 0 := by
        simpa [addressToWord] using h_authorized_prop
      first
      | intro h_same
        subst h_same
        simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
          balances, msgSender, getMappingUint, getMappingUintAddr, getMapping2,
          setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
          h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
          h_authorized_prop_raw, addressToWord]
      | intro h_ne h_insufficient
        have h_insufficient_raw : (s.storageMap 3 fromAddr).val < 1 := by
          simpa using h_insufficient
        have h_not_balance : ¬ 1 ≤ (s.storageMap 3 fromAddr).val := by omega
        simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
          balances, msgSender, getMappingUint, getMappingUintAddr, getMapping2,
          getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, h_to_nonzero_raw, h_exists_raw, h_owner_raw,
          h_from_word_nonzero_raw, h_authorized_prop_raw, h_ne, h_not_balance,
          addressToWord]
      | intro h_ne h_balance h_overflow
        have h_balance_raw : 1 ≤ (s.storageMap 3 fromAddr).val := by
          simpa using h_balance
        have h_overflow_raw :
            Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by
          simpa using h_overflow
        simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
          balances, msgSender, getMappingUint, getMappingUintAddr, getMapping2,
          getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_to_nonzero_raw, h_exists_raw, h_owner_raw,
          h_from_word_nonzero_raw, h_authorized_prop_raw, h_ne, h_balance_raw,
          h_overflow_raw, addressToWord]
      | intro h_ne h_balance h_no_overflow
        have h_balance_raw : 1 ≤ (s.storageMap 3 fromAddr).val := by
          simpa using h_balance
        have h_no_overflow_raw :
            (s.storageMap 3 toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
          simpa using h_no_overflow
        have h_not_overflow :
            ¬ Verity.Stdlib.Math.MAX_UINT256 <
              (s.storageMap 3 toAddr).val + 1 := by
          omega
        simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
          balances, msgSender, getMappingUint, getMappingUintAddr, getMapping2, getMapping,
          setMapping, setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
          h_authorized_prop_raw, h_ne, h_balance_raw, h_not_overflow, addressToWord]

-- tama: discharges=erc721_transferFrom_reverts_for_zero_recipient
theorem transferFrom_reverts_for_zero_recipient
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_for_zero_recipient fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_zero

-- tama: discharges=erc721_transferFrom_reverts_when_token_is_missing
theorem transferFrom_reverts_when_token_is_missing
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_when_token_is_missing fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_missing

-- tama: discharges=erc721_transferFrom_reverts_when_from_is_not_owner
theorem transferFrom_reverts_when_from_is_not_owner
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_when_from_is_not_owner fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_wrong_owner

-- tama: discharges=erc721_transferFrom_reverts_when_sender_is_not_authorized
theorem transferFrom_reverts_when_sender_is_not_authorized
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_when_sender_is_not_authorized fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_not_auth

-- tama: discharges=erc721_transferFrom_to_self_succeeds
theorem transferFrom_to_self_succeeds
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_to_self_succeeds fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_self_succeeds

-- tama: discharges=erc721_transferFrom_to_self_keeps_balances
theorem transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_to_self_keeps_balances fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_self_balances

-- tama: discharges=erc721_transferFrom_sets_owner_on_self_transfer
theorem transferFrom_sets_owner_on_self_transfer
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_sets_owner_on_self_transfer fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_self_owner

-- tama: discharges=erc721_transferFrom_clears_approval_on_self_transfer
theorem transferFrom_clears_approval_on_self_transfer
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_clears_approval_on_self_transfer fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_self_approval

-- tama: discharges=erc721_transferFrom_reverts_when_from_balance_is_low
theorem transferFrom_reverts_when_from_balance_is_low
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_when_from_balance_is_low fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_low_balance

-- tama: discharges=erc721_transferFrom_reverts_when_to_balance_would_overflow
theorem transferFrom_reverts_when_to_balance_would_overflow
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_reverts_when_to_balance_would_overflow fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_to_overflow

-- tama: discharges=erc721_transferFrom_between_distinct_accounts_succeeds
theorem transferFrom_between_distinct_accounts_succeeds
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_between_distinct_accounts_succeeds fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_between_succeeds

-- tama: discharges=erc721_transferFrom_sets_new_owner
theorem transferFrom_sets_new_owner
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_sets_new_owner fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, h_sets_owner, _h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_sets_owner

-- tama: discharges=erc721_transferFrom_clears_token_approval
theorem transferFrom_clears_token_approval
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_clears_token_approval fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, h_clears_approval,
      _h_debits, _h_credits⟩
  exact h_clears_approval

-- tama: discharges=erc721_transferFrom_debits_from_balance
theorem transferFrom_debits_from_balance
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_debits_from_balance fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      h_debits, _h_credits⟩
  exact h_debits

-- tama: discharges=erc721_transferFrom_credits_to_balance
theorem transferFrom_credits_to_balance
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_credits_to_balance fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  rcases transferFrom_properties_after_run fromAddr toAddr tokenId s with
    ⟨_h_zero, _h_missing, _h_wrong_owner, _h_not_auth, _h_self_succeeds,
      _h_self_balances, _h_self_owner, _h_self_approval, _h_low_balance,
      _h_to_overflow, _h_between_succeeds, _h_sets_owner, _h_clears_approval,
      _h_debits, h_credits⟩
  exact h_credits

  end Tamago.Proof.Tokens.ERC721Proof
