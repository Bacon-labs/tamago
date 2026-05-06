import spec.ERC721Spec
import Verity.Proofs.Stdlib.Automation

namespace proof.ERC721Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open spec.ERC721Spec
open src.ERC721

attribute [local simp] contractOwner tokenSupply nextTokenId balances tokenOwners tokenApprovals operatorApprovals

-- tama: discharges=erc721_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc721_totalSupply_spec ((totalSupply).run s).fst s := by
  simp [erc721_totalSupply_spec, totalSupply, tokenSupply, Bind.bind, Pure.pure]

-- tama: discharges=erc721_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  erc721_owner_spec ((owner).run s).fst s := by
  simp [erc721_owner_spec, owner, contractOwner, Bind.bind, Pure.pure]

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

-- tama: discharges=erc721_setApprovalForAll_effect
theorem setApprovalForAll_updates_operator_slot
    (operator : Address) (approved : Bool) (s : ContractState) :
  erc721_setApprovalForAll_effect operator approved s ((setApprovalForAll operator approved).run s) := by
  unfold erc721_setApprovalForAll_effect
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases approved <;>
      simp [setApprovalForAll, operatorApprovals, src.boolToWord, msgSender,
        setMapping2, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure]
  · simp [setApprovalForAll, operatorApprovals, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [setApprovalForAll, operatorApprovals, tokenSupply, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [setApprovalForAll, operatorApprovals, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx key
    simp [setApprovalForAll, operatorApprovals, msgSender, setMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=erc721_approve_effect
theorem approve_updates_token_approval_when_authorized
    (approved : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_approve_effect approved tokenId s ((approve approved tokenId).run s) := by
  unfold erc721_approve_effect
  refine ⟨?_, ?_⟩
  · intro h_missing
    have h_missing_raw : s.storageMapUint 4 tokenId = 0 := by
      simpa using h_missing
    simp [approve, tokenOwners, tokenApprovals, operatorApprovals, getMappingUint,
      getMapping2, setMappingUintAddr, msgSender, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, h_missing_raw]
  · intro h_exists
    have h_exists_raw : (s.storageMapUint 4 tokenId != 0) = true := by
      simpa using h_exists
    refine ⟨?_, ?_⟩
    · intro h_unauthorized
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
    · intro h_authorized
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
      refine ⟨?_, ?_⟩ <;>
        simp [approve, tokenOwners, tokenApprovals, operatorApprovals, getMappingUint,
          getMapping2, setMappingUintAddr, setMappingUint, msgSender, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
          h_exists_raw, h_authorized_prop_raw, wordToAddress, addressToWord]

-- tama: discharges=erc721_mint_effect
theorem mint_updates_owner_balance_supply_and_counter
    (toAddr : Address) (s : ContractState) :
  erc721_mint_effect toAddr s ((mint toAddr).run s) := by
  unfold erc721_mint_effect
  refine ⟨?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa using h_not_owner
    simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_owner_raw]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    refine ⟨?_, ?_⟩
    · intro h_zero
      have h_zero_raw : toAddr = 0 := by
        simpa [zeroAddress] using h_zero
      subst h_zero_raw
      simp [mint, contractOwner, zeroAddress, msgSender, getStorageAddr, Contract.run,
        Verity.bind, Bind.bind, Verity.require, h_owner_raw]
    · intro h_recipient
      have h_recipient_raw : ¬ toAddr = 0 := by
        simpa [zeroAddress] using h_recipient
      refine ⟨?_, ?_⟩
      · intro h_minted
        have h_minted_raw : s.storageMapUint 4 (s.storage 2) ≠ 0 := by
          simpa using h_minted
        simp [mint, contractOwner, zeroAddress, nextTokenId, tokenOwners, msgSender,
          getStorageAddr, getStorage, getMappingUint, Contract.run, Verity.bind,
          Bind.bind, Verity.require, h_owner_raw, h_recipient_raw, h_minted_raw]
      · intro h_unminted
        have h_unminted_raw : s.storageMapUint 4 (s.storage 2) = 0 := by
          simpa using h_unminted
        refine ⟨?_, ?_⟩
        · intro h_balance_overflow
          have h_overflow :
              Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by
            simpa using h_balance_overflow
          simp [mint, contractOwner, zeroAddress, balances, nextTokenId, tokenOwners,
            msgSender, getStorageAddr, getStorage, getMappingUint, getMapping, Contract.run,
            Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_owner_raw, h_recipient_raw, h_unminted_raw,
            h_overflow]
        · intro h_balance_no_overflow
          have h_balance_no_overflow_raw :
              (s.storageMap 3 toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
            simpa using h_balance_no_overflow
          have h_not_balance_overflow :
              ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 3 toAddr).val + 1 := by
            omega
          refine ⟨?_, ?_⟩
          · intro h_supply_overflow
            have h_overflow :
                Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + 1 := by
              simpa using h_supply_overflow
            simp [mint, contractOwner, zeroAddress, balances, tokenSupply, nextTokenId,
              tokenOwners, msgSender, getStorageAddr, getStorage, getMappingUint, getMapping,
              Contract.run, Verity.bind, Bind.bind, Verity.require,
              Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw,
              h_recipient_raw, h_unminted_raw, h_not_balance_overflow, h_overflow,
              Verity.pure, Pure.pure]
          · intro h_supply_no_overflow
            have h_supply_no_overflow_raw :
                (s.storage 1).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
              simpa using h_supply_no_overflow
            have h_not_supply_overflow :
                ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + 1 := by
              omega
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [mint, contractOwner, zeroAddress, balances, tokenSupply, nextTokenId,
                tokenOwners, msgSender, getStorageAddr, getStorage, getMappingUint, getMapping,
                setMappingUintAddr, setMappingUint, setMapping, setStorage, Contract.run,
                ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw,
                h_recipient_raw, h_unminted_raw, h_not_balance_overflow,
                h_not_supply_overflow, Verity.pure, Pure.pure]

-- tama: discharges=erc721_transferFrom_effect
theorem transferFrom_effect_after_run
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState) :
  erc721_transferFrom_effect fromAddr toAddr tokenId s
    ((transferFrom fromAddr toAddr tokenId).run s) := by
  unfold erc721_transferFrom_effect
  refine ⟨?_, ?_⟩
  · intro h_zero
    have h_zero_raw : toAddr = 0 := by
      simpa [zeroAddress] using h_zero
    subst h_zero_raw
    simp [transferFrom, zeroAddress, msgSender, Contract.run, Verity.bind, Bind.bind,
      Verity.require]
  · intro h_to_nonzero
    have h_to_nonzero_raw : ¬ toAddr = 0 := by
      simpa [zeroAddress] using h_to_nonzero
    refine ⟨?_, ?_⟩
    · intro h_missing
      have h_missing_raw : s.storageMapUint 4 tokenId = 0 := by
        simpa using h_missing
      simp [transferFrom, zeroAddress, tokenOwners, msgSender, getMappingUint, Contract.run,
        Verity.bind, Bind.bind, Verity.require, h_to_nonzero_raw, h_missing_raw]
    · intro h_exists
      have h_exists_raw : s.storageMapUint 4 tokenId ≠ 0 := by
        simpa using h_exists
      refine ⟨?_, ?_⟩
      · intro h_wrong_owner
        have h_wrong_owner_raw :
            s.storageMapUint 4 tokenId ≠ addressToWord fromAddr := by
          simpa using h_wrong_owner
        have h_wrong_owner_raw' :
            s.storageMapUint 4 tokenId ≠ Core.Uint256.ofNat (Core.Address.toNat fromAddr) := by
          simpa [addressToWord] using h_wrong_owner_raw
        simp [transferFrom, zeroAddress, tokenOwners, msgSender, getMappingUint, Contract.run,
          Verity.bind, Bind.bind, Verity.require, h_to_nonzero_raw, h_exists_raw,
          h_wrong_owner_raw', addressToWord]
      · intro h_owner
        have h_owner_raw :
            s.storageMapUint 4 tokenId = addressToWord fromAddr := by
          simpa using h_owner
        have h_from_word_nonzero : addressToWord fromAddr ≠ 0 := by
          rw [← h_owner_raw]
          exact h_exists_raw
        have h_from_word_nonzero_raw :
            Core.Uint256.ofNat (Core.Address.toNat fromAddr) ≠ 0 := by
          simpa [addressToWord] using h_from_word_nonzero
        refine ⟨?_, ?_⟩
        · intro h_not_authorized
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
        · intro h_authorized
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
          refine ⟨?_, ?_⟩
          · intro h_same
            subst h_same
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
                balances, msgSender, getMappingUint, getMappingUintAddr, getMapping2,
                setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
                Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
                h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
                h_authorized_prop_raw,
                addressToWord]
          · intro h_ne
            refine ⟨?_, ?_⟩
            · intro h_insufficient
              have h_insufficient_raw : (s.storageMap 3 fromAddr).val < 1 := by
                simpa using h_insufficient
              have h_not_balance : ¬ 1 ≤ (s.storageMap 3 fromAddr).val := by omega
              simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals, operatorApprovals,
                balances, msgSender, getMappingUint, getMappingUintAddr, getMapping2,
                getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
                Verity.require, h_to_nonzero_raw, h_exists_raw, h_owner_raw,
                h_from_word_nonzero_raw, h_authorized_prop_raw, h_ne, h_not_balance,
                addressToWord]
            · intro h_balance
              have h_balance_raw : 1 ≤ (s.storageMap 3 fromAddr).val := by
                simpa using h_balance
              refine ⟨?_, ?_⟩
              · intro h_overflow
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
              · intro h_no_overflow
                have h_no_overflow_raw :
                    (s.storageMap 3 toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
                  simpa using h_no_overflow
                have h_not_overflow :
                    ¬ Verity.Stdlib.Math.MAX_UINT256 <
                      (s.storageMap 3 toAddr).val + 1 := by
                  omega
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals,
                    operatorApprovals, balances, msgSender, getMappingUint,
                    getMappingUintAddr, getMapping2, getMapping, setMapping,
                    setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
                    Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
                    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                    h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
                    h_authorized_prop_raw, h_ne, h_balance_raw, h_not_overflow, addressToWord]
                · simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals,
                    operatorApprovals, balances, msgSender, getMappingUint,
                    getMappingUintAddr, getMapping2, getMapping, setMapping,
                    setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
                    Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
                    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                    h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
                    h_authorized_prop_raw, h_ne, h_balance_raw, h_not_overflow, addressToWord]
                · simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals,
                    operatorApprovals, balances, msgSender, getMappingUint,
                    getMappingUintAddr, getMapping2, getMapping, setMapping,
                    setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
                    Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
                    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                    h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
                    h_authorized_prop_raw, h_ne, h_balance_raw, h_not_overflow, addressToWord]
                · simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals,
                    operatorApprovals, balances, msgSender, getMappingUint,
                    getMappingUintAddr, getMapping2, getMapping, setMapping,
                    setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
                    Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
                    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                    h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
                    h_authorized_prop_raw, h_ne, h_balance_raw, h_not_overflow, addressToWord]
                · simp [transferFrom, zeroAddress, tokenOwners, tokenApprovals,
                    operatorApprovals, balances, msgSender, getMappingUint,
                    getMappingUintAddr, getMapping2, getMapping, setMapping,
                    setMappingUintAddr, setMappingUint, Contract.run, ContractResult.snd,
                    Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure,
                    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                    h_to_nonzero_raw, h_exists_raw, h_owner_raw, h_from_word_nonzero_raw,
                    h_authorized_prop_raw, h_ne, h_balance_raw, h_not_overflow, addressToWord]

end proof.ERC721Proof
