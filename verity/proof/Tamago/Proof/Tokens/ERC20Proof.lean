import Tamago.Spec.Tokens.ERC20Spec
import Tamago.Proof.Auth.OwnableProof
import Tamago.Proof.EventSimp
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Tokens.ERC20Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Tamago.Spec.Tokens.ERC20Spec
open Tamago.Tokens.ERC20

attribute [local simp] contractOwner tokenSupply balances allowances tokenDecimals
  Tamago.Tokens.ERC20Base.contractOwner Tamago.Tokens.ERC20Base.tokenSupply Tamago.Tokens.ERC20Base.balances
  Tamago.Tokens.ERC20Base.allowances Tamago.Tokens.ERC20Base.maxUint256
  Tamago.Tokens.ERC20Base.__verity_immutable_slot_tokenDecimals
  Tamago.Tokens.ERC20Base.decimals Tamago.Tokens.ERC20Base.totalSupply Tamago.Tokens.ERC20Base.balanceOf
  Tamago.Tokens.ERC20Base.allowance Tamago.Tokens.ERC20Base.owner Tamago.Tokens.ERC20Base.transferOwnership
  Tamago.Tokens.ERC20Base.renounceOwnership Tamago.Tokens.ERC20Base.approve Tamago.Tokens.ERC20Base.transfer
  Tamago.Tokens.ERC20Base.transferFrom Tamago.Tokens.ERC20Base.mint Tamago.Tokens.ERC20Base.burn
  Tamago.Auth.OwnableBase.contractOwner Tamago.Auth.OwnableBase.transferOwnership
  Tamago.Auth.OwnableBase.renounceOwnership Contracts.emit emitEvent

-- tama: discharges=erc20_decimals_spec
theorem decimals_returns_storage_decimals (s : ContractState) :
  erc20_decimals_spec ((decimals).run s).fst s := by
  simp [erc20_decimals_spec, decimals, tokenDecimals, getStorage, Contract.run,
    ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc20_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc20_totalSupply_spec ((totalSupply).run s).fst s := by
  simp [erc20_totalSupply_spec, totalSupply, tokenSupply, getStorage, Contract.run,
    ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc20_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc20_balanceOf_spec account ((balanceOf account).run s).fst s := by
  simp [erc20_balanceOf_spec, balanceOf, balances, getStorage, getMapping,
    Contract.run, ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc20_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  erc20_allowance_spec ownerAddr spender ((allowance ownerAddr spender).run s).fst s := by
  simp [erc20_allowance_spec, allowance, allowances, getStorage, getMapping2,
    Contract.run, ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc20_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  erc20_owner_spec ((owner).run s).fst s := by
  simp [erc20_owner_spec, Tamago.Spec.Auth.OwnableSpec.ownable_owner_spec, owner, contractOwner,
    Tamago.Auth.Ownable.contractOwner, getStorage, getStorageAddr, Contract.run, ContractResult.fst,
    Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc20_transferOwnership_reverts_for_non_owner
theorem transferOwnership_reverts_for_non_owner (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_reverts_for_non_owner newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_reverts_for_non_owner,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_reverts_for_non_owner newOwner s

-- tama: discharges=erc20_transferOwnership_reverts_for_zero_owner
theorem transferOwnership_reverts_for_zero_owner (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_reverts_for_zero_owner newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_reverts_for_zero_owner,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_reverts_for_zero_owner newOwner s

-- tama: discharges=erc20_transferOwnership_succeeds_for_owner_to_nonzero
theorem transferOwnership_succeeds_for_owner_to_nonzero (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_succeeds_for_owner_to_nonzero newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_succeeds_for_owner_to_nonzero,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_succeeds_for_owner_to_nonzero newOwner s

-- tama: discharges=erc20_transferOwnership_sets_new_owner
theorem transferOwnership_sets_new_owner (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_sets_new_owner newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_sets_new_owner,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_sets_new_owner newOwner s

-- tama: discharges=erc20_transferOwnership_keeps_other_owner_slots
theorem transferOwnership_keeps_other_owner_slots (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_keeps_other_owner_slots newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_keeps_other_owner_slots,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_other_owner_slots newOwner s

-- tama: discharges=erc20_transferOwnership_keeps_uint_storage
theorem transferOwnership_keeps_uint_storage (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_keeps_uint_storage newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_keeps_uint_storage,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_uint_storage newOwner s

-- tama: discharges=erc20_transferOwnership_keeps_balances_and_allowances
theorem transferOwnership_keeps_balances_and_allowances (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_keeps_balances_and_allowances newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_keeps_balances_and_allowances,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_balances_and_allowances newOwner s

-- tama: discharges=erc20_transferOwnership_keeps_array_storage
theorem transferOwnership_keeps_array_storage (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_keeps_array_storage newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_keeps_array_storage,
    transferOwnership, Tamago.Auth.Ownable.transferOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.transferOwnership_keeps_array_storage newOwner s

-- tama: discharges=erc20_renounceOwnership_reverts_for_non_owner
theorem renounceOwnership_reverts_for_non_owner (s : ContractState) :
  erc20_renounceOwnership_reverts_for_non_owner s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_reverts_for_non_owner,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_reverts_for_non_owner s

-- tama: discharges=erc20_renounceOwnership_succeeds_for_owner
theorem renounceOwnership_succeeds_for_owner (s : ContractState) :
  erc20_renounceOwnership_succeeds_for_owner s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_succeeds_for_owner,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_succeeds_for_owner s

-- tama: discharges=erc20_renounceOwnership_clears_owner
theorem renounceOwnership_clears_owner (s : ContractState) :
  erc20_renounceOwnership_clears_owner s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_clears_owner,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_clears_owner s

-- tama: discharges=erc20_renounceOwnership_keeps_other_owner_slots
theorem renounceOwnership_keeps_other_owner_slots (s : ContractState) :
  erc20_renounceOwnership_keeps_other_owner_slots s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_keeps_other_owner_slots,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_other_owner_slots s

-- tama: discharges=erc20_renounceOwnership_keeps_uint_storage
theorem renounceOwnership_keeps_uint_storage (s : ContractState) :
  erc20_renounceOwnership_keeps_uint_storage s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_keeps_uint_storage,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_uint_storage s

-- tama: discharges=erc20_renounceOwnership_keeps_balances_and_allowances
theorem renounceOwnership_keeps_balances_and_allowances (s : ContractState) :
  erc20_renounceOwnership_keeps_balances_and_allowances s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_keeps_balances_and_allowances,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_balances_and_allowances s

-- tama: discharges=erc20_renounceOwnership_keeps_array_storage
theorem renounceOwnership_keeps_array_storage (s : ContractState) :
  erc20_renounceOwnership_keeps_array_storage s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_keeps_array_storage,
    renounceOwnership, Tamago.Auth.Ownable.renounceOwnership, contractOwner, Tamago.Auth.Ownable.contractOwner,
    getStorage, Contract.run, ContractResult.fst, Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using Tamago.Proof.Auth.OwnableProof.renounceOwnership_keeps_array_storage s

private theorem approve_properties_after_run (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_succeeds spender amount s ((approve spender amount).run s) ∧
  erc20_approve_sets_allowance spender amount s ((approve spender amount).run s) ∧
  erc20_approve_keeps_balances spender amount s ((approve spender amount).run s) ∧
  erc20_approve_keeps_total_supply spender amount s ((approve spender amount).run s) := by
  unfold erc20_approve_succeeds erc20_approve_sets_allowance
    erc20_approve_keeps_balances erc20_approve_keeps_total_supply
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=erc20_approve_succeeds
theorem approve_succeeds (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_succeeds spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).1

-- tama: discharges=erc20_approve_sets_allowance
theorem approve_sets_allowance (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_sets_allowance spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.1

-- tama: discharges=erc20_approve_keeps_balances
theorem approve_keeps_balances (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_keeps_balances spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.2.1

-- tama: discharges=erc20_approve_keeps_total_supply
theorem approve_keeps_total_supply (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_keeps_total_supply spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.2.2

private theorem transfer_properties_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_reverts_when_balance_is_low toAddr amount s ((transfer toAddr amount).run s) ∧
  erc20_transfer_to_self_keeps_balances toAddr amount s ((transfer toAddr amount).run s) ∧
  erc20_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s ((transfer toAddr amount).run s) ∧
  erc20_transfer_moves_tokens_between_distinct_accounts toAddr amount s ((transfer toAddr amount).run s) ∧
  erc20_transfer_keeps_total_supply toAddr amount s ((transfer toAddr amount).run s) := by
  unfold erc20_transfer_reverts_when_balance_is_low
    erc20_transfer_to_self_keeps_balances
    erc20_transfer_reverts_when_recipient_balance_would_overflow
    erc20_transfer_moves_tokens_between_distinct_accounts erc20_transfer_keeps_total_supply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h_insufficient
    have h_insufficient_raw : amount.val > (s.storageMap 2 s.sender).val := by
      simpa using h_insufficient
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 s.sender).val := by omega
    simp [transfer, balances, msgSender, getMapping, Contract.run, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind,
      Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_not_balance]
  · intro h_balance h_same
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    subst h_same
    simp [transfer, balances, tokenSupply, msgSender, getMapping, Contract.run, ContractResult.snd,
      Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_balance_raw]
  · intro h_balance h_ne h_overflow
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_overflow_strict :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val := by
      simpa using h_overflow
    simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
      ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
      h_overflow_strict]
  · intro h_balance h_ne h_no_overflow
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_no_overflow_raw :
        (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_no_overflow
    have h_not_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
        h_not_overflow]
    · show ((transfer toAddr amount).run s).snd.storageMap 2 s.sender =
        sub (s.storageMap 2 s.sender) amount
      simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
        h_not_overflow]
    · simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
        h_not_overflow, HSub.hSub]
  · by_cases h_balance : amount.val ≤ (s.storageMap 2 s.sender).val
    · by_cases h_same : s.sender = toAddr
      · subst h_same
        simp [transfer, balances, tokenSupply, msgSender, getMapping, Contract.run,
          ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
          h_balance]
      · by_cases h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val
        · simp [transfer, balances, tokenSupply, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance, h_same,
          h_overflow]
        · simp [transfer, balances, tokenSupply, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance, h_same,
          h_overflow]
    · simp [transfer, balances, tokenSupply, msgSender, getMapping, Contract.run,
        ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_balance]

-- tama: discharges=erc20_transfer_reverts_when_balance_is_low
theorem transfer_reverts_when_balance_is_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_reverts_when_balance_is_low toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).1

-- tama: discharges=erc20_transfer_to_self_keeps_balances
theorem transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_to_self_keeps_balances toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.1

-- tama: discharges=erc20_transfer_reverts_when_recipient_balance_would_overflow
theorem transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s
    ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.1

-- tama: discharges=erc20_transfer_moves_tokens_between_distinct_accounts
theorem transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.1

-- tama: discharges=erc20_transfer_keeps_total_supply
theorem transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_keeps_total_supply toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.2

private theorem transferFrom_properties_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_to_self_keeps_balances fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_keeps_total_supply fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  erc20_transferFrom_spends_finite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) := by
  unfold erc20_transferFrom_reverts_when_allowance_is_low
    erc20_transferFrom_reverts_when_balance_is_low
    erc20_transferFrom_reverts_when_recipient_balance_would_overflow
    erc20_transferFrom_to_self_keeps_balances
    erc20_transferFrom_moves_tokens_between_distinct_accounts
    erc20_transferFrom_keeps_total_supply erc20_transferFrom_keeps_infinite_allowance
    erc20_transferFrom_spends_finite_allowance
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_insufficient_allowance
    have h_insufficient_allowance_raw :
        amount.val > (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_insufficient_allowance
    have h_not_allowance :
        ¬ amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by omega
    simp [transferFrom, allowances, msgSender, getMapping2, Contract.run, Verity.bind,
      getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_not_allowance]
  · intro h_allowance h_insufficient_balance
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    have h_insufficient_balance_raw :
        amount.val > (s.storageMap 2 fromAddr).val := by
      simpa using h_insufficient_balance
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 fromAddr).val := by omega
    simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
      Contract.run, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance_raw, h_not_balance]
  · intro h_allowance h_balance h_ne h_overflow
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_overflow_strict :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val := by
      simpa using h_overflow
    simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping, setMapping,
      Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Pure.pure, Verity.pure,
      Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_allowance_raw, h_balance_raw, h_ne, h_overflow_strict]
  · intro h_allowance h_balance h_eq
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    subst h_eq
    by_cases h_max :
        s.storageMap2 3 fromAddr s.sender =
          maxUint256
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
      have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
        simpa [h_max, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] using h_allowance_raw
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure,
        Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance_raw, h_allowance_max, h_balance_raw, h_max]
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure,
        Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance_raw, h_balance_raw, h_max]
  · intro h_allowance h_balance h_ne h_no_overflow
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_no_overflow_raw :
        (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_no_overflow
    have h_not_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val := by omega
    by_cases h_max :
        s.storageMap2 3 fromAddr s.sender =
          maxUint256
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
      have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
        simpa [h_max, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] using h_allowance_raw
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
          setMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind,
          Pure.pure, Verity.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_allowance_raw, h_balance_raw, h_ne, h_not_overflow,
          h_allowance_max, h_max, HSub.hSub]
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
          setMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind,
          Pure.pure, Verity.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_allowance_raw, h_balance_raw, h_ne, h_not_overflow,
          h_max, HSub.hSub]
  · by_cases h_allowance : amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val
    · by_cases h_balance : amount.val ≤ (s.storageMap 2 fromAddr).val
      · by_cases h_same : fromAddr = toAddr
        · subst h_same
          by_cases h_max :
              s.storageMap2 3 fromAddr s.sender =
                maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
            have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
              simpa [h_max, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] using h_allowance
            simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
              getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind,
              Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance, h_allowance_max, h_balance,
              h_max]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
            simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
              getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind,
              Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance, h_balance, h_max]
        · by_cases h_overflow :
            Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val
          · simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
              getMapping, setMapping, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind,
              Pure.pure, Verity.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
              Verity.Stdlib.Math.safeAdd, h_allowance, h_balance, h_same, h_overflow]
          · by_cases h_max :
              s.storageMap2 3 fromAddr s.sender =
                maxUint256
            · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
              have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
                simpa [h_max, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] using h_allowance
              simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
                getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
                Verity.bind, getStorage, ContractResult.fst, Bind.bind, Pure.pure, Verity.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
                Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_allowance,
                h_allowance_max, h_balance, h_same, h_overflow, h_max]
            · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max
              simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
                getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
                Verity.bind, getStorage, ContractResult.fst, Bind.bind, Pure.pure, Verity.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
                Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_allowance,
                h_balance, h_same, h_overflow, h_max]
      · simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2, getMapping,
          Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance,
          h_balance]
    · simp [transferFrom, allowances, tokenSupply, msgSender, getMapping2, Contract.run,
        ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance]
  · intro h_allowance h_balance h_path h_max
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_max_ofNat :
        s.storageMap2 3 fromAddr s.sender =
          maxUint256 := by
      change s.storageMap2 3 fromAddr s.sender =
        maxUint256
      simpa using h_max
    simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_max_ofNat
    have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
      simpa [h_max_ofNat, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] using h_allowance_raw
    rcases h_path with h_eq | ⟨h_ne, h_no_overflow⟩
    · subst h_eq
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure,
        Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance_raw, h_allowance_max, h_balance_raw,
        h_max_ofNat, emitEvent]
    · have h_no_overflow_raw :
          (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_no_overflow
      have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val := by omega
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        setMapping, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure,
        Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_allowance_raw, h_allowance_max, h_balance_raw, h_ne,
        h_not_overflow, h_max_ofNat]
  · intro h_allowance h_balance h_path h_not_max
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_not_max_ofNat :
        s.storageMap2 3 fromAddr s.sender ≠
          maxUint256 := by
      change s.storageMap2 3 fromAddr s.sender ≠
        maxUint256
      simpa using h_not_max
    simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure] at h_not_max_ofNat
    rcases h_path with h_eq | ⟨h_ne, h_no_overflow⟩
    · subst h_eq
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind, Verity.pure,
        Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_allowance_raw, h_balance_raw, h_not_max_ofNat]
    · have h_no_overflow_raw :
          (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_no_overflow
      have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val := by omega
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        setMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind, getStorage, ContractResult.fst, Bind.bind,
        Verity.pure, Pure.pure, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_allowance_raw, h_balance_raw, h_ne, h_not_overflow,
        h_not_max_ofNat]

-- tama: discharges=erc20_transferFrom_reverts_when_allowance_is_low
theorem transferFrom_reverts_when_allowance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).1

-- tama: discharges=erc20_transferFrom_reverts_when_balance_is_low
theorem transferFrom_reverts_when_balance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.1

-- tama: discharges=erc20_transferFrom_reverts_when_recipient_balance_would_overflow
theorem transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.1

-- tama: discharges=erc20_transferFrom_to_self_keeps_balances
theorem transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_to_self_keeps_balances fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.1

-- tama: discharges=erc20_transferFrom_moves_tokens_between_distinct_accounts
theorem transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.1

-- tama: discharges=erc20_transferFrom_keeps_total_supply
theorem transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_keeps_total_supply fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.1

-- tama: discharges=erc20_transferFrom_keeps_infinite_allowance
theorem transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.2.1

-- tama: discharges=erc20_transferFrom_spends_finite_allowance
theorem transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_spends_finite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.2.2

private theorem mint_properties_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_reverts_for_non_owner toAddr amount s ((mint toAddr amount).run s) ∧
  erc20_mint_reverts_when_total_supply_would_overflow toAddr amount s ((mint toAddr amount).run s) ∧
  erc20_mint_succeeds_when_owner_and_no_overflow toAddr amount s ((mint toAddr amount).run s) ∧
  erc20_mint_credits_recipient toAddr amount s ((mint toAddr amount).run s) ∧
  erc20_mint_increases_total_supply toAddr amount s ((mint toAddr amount).run s) ∧
  erc20_mint_keeps_owner toAddr amount s ((mint toAddr amount).run s) := by
  unfold erc20_mint_reverts_for_non_owner
    erc20_mint_reverts_when_total_supply_would_overflow
    erc20_mint_succeeds_when_owner_and_no_overflow erc20_mint_credits_recipient
    erc20_mint_increases_total_supply erc20_mint_keeps_owner
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa using h_not_owner
    simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind,
      Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_not_owner_raw]
  · intro h_owner h_supply_overflow
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storage 1).val + amount.val := by
      simpa using h_supply_overflow
    simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
      getMapping, getStorage, Contract.run, Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw,
      h_overflow, ContractResult.snd, Verity.pure, Pure.pure]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_supply_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + amount.val
      · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
          getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
          Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow]
      · by_cases h_balance_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
            Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow, h_balance_overflow]
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
            Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_owner_raw, h_supply_overflow, h_balance_overflow,
            Verity.pure, Pure.pure]
    · simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
        Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_supply_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + amount.val
      · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
          getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
          Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow]
      · by_cases h_balance_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
            Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow, h_balance_overflow]
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
            Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_owner_raw, h_supply_overflow, h_balance_overflow,
            Verity.pure, Pure.pure]
    · simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
        Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_supply_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + amount.val
      · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
          getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
          Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow]
      · by_cases h_balance_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
            Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow, h_balance_overflow]
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
            Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_owner_raw, h_supply_overflow, h_balance_overflow,
            Verity.pure, Pure.pure]
    · simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
        Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw]
  · by_cases h_owner_raw : s.sender = s.storageAddr 0
    · by_cases h_supply_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + amount.val
      · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
          getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
          Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow]
      · by_cases h_balance_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind, ContractResult.fst, Bind.bind,
            Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            Verity.pure, Pure.pure, h_owner_raw, h_supply_overflow, h_balance_overflow]
        · simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
            Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_owner_raw, h_supply_overflow, h_balance_overflow,
            Verity.pure, Pure.pure]
    · simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
        Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw]

-- tama: discharges=erc20_mint_reverts_for_non_owner
theorem mint_reverts_for_non_owner (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_reverts_for_non_owner toAddr amount s ((mint toAddr amount).run s) :=
  (mint_properties_after_run toAddr amount s).1

-- tama: discharges=erc20_mint_reverts_when_total_supply_would_overflow
theorem mint_reverts_when_total_supply_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_reverts_when_total_supply_would_overflow toAddr amount s
    ((mint toAddr amount).run s) :=
  (mint_properties_after_run toAddr amount s).2.1

-- tama: discharges=erc20_mint_succeeds_when_owner_and_no_overflow
theorem mint_succeeds_when_owner_and_no_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_succeeds_when_owner_and_no_overflow toAddr amount s
    ((mint toAddr amount).run s) :=
  (mint_properties_after_run toAddr amount s).2.2.1

-- tama: discharges=erc20_mint_credits_recipient
theorem mint_credits_recipient (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_credits_recipient toAddr amount s ((mint toAddr amount).run s) :=
  (mint_properties_after_run toAddr amount s).2.2.2.1

-- tama: discharges=erc20_mint_increases_total_supply
theorem mint_increases_total_supply (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_increases_total_supply toAddr amount s ((mint toAddr amount).run s) :=
  (mint_properties_after_run toAddr amount s).2.2.2.2.1

-- tama: discharges=erc20_mint_keeps_owner
theorem mint_keeps_owner (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_keeps_owner toAddr amount s ((mint toAddr amount).run s) :=
  (mint_properties_after_run toAddr amount s).2.2.2.2.2

private theorem burn_properties_after_run (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_reverts_for_non_owner fromAddr amount s ((burn fromAddr amount).run s) ∧
  erc20_burn_reverts_when_balance_is_low fromAddr amount s ((burn fromAddr amount).run s) ∧
  erc20_burn_reverts_when_total_supply_is_low fromAddr amount s ((burn fromAddr amount).run s) ∧
  erc20_burn_succeeds_when_owner_has_balance_and_supply fromAddr amount s ((burn fromAddr amount).run s) ∧
  erc20_burn_debits_account fromAddr amount s ((burn fromAddr amount).run s) ∧
  erc20_burn_decreases_total_supply fromAddr amount s ((burn fromAddr amount).run s) := by
  unfold erc20_burn_reverts_for_non_owner
    erc20_burn_reverts_when_balance_is_low erc20_burn_reverts_when_total_supply_is_low
    erc20_burn_succeeds_when_owner_has_balance_and_supply erc20_burn_debits_account
    erc20_burn_decreases_total_supply
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa using h_not_owner
    simp [burn, contractOwner, msgSender, getStorageAddr, Contract.run, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind,
      Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_not_owner_raw]
  · intro h_owner h_insufficient_balance
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_insufficient_balance_raw :
        amount.val > (s.storageMap 2 fromAddr).val := by
      simpa using h_insufficient_balance
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 fromAddr).val := by omega
    simp [burn, contractOwner, balances, msgSender, getStorageAddr, getMapping,
      Contract.run, Verity.bind, getStorage, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw, h_not_balance]
  · intro h_owner h_balance h_insufficient_supply
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_insufficient_supply_raw :
        amount.val > (s.storage 1).val := by
      simpa using h_insufficient_supply
    have h_not_supply : ¬ amount.val ≤ (s.storage 1).val := by omega
    simp [burn, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
      getMapping, getStorage, Contract.run, Verity.bind, ContractResult.fst, Verity.pure, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require,
      h_owner_raw, h_balance_raw, h_not_supply]
  · intro h_owner h_balance h_supply
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    simp [burn, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
      getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw, h_balance_raw, h_supply_raw,
      Verity.pure, Pure.pure]
  · intro h_owner h_balance h_supply
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    simp [burn, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
      getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw, h_balance_raw, h_supply_raw,
      Verity.pure, Pure.pure]
  · intro h_owner h_balance h_supply
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    simp [burn, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
      getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, ContractResult.fst, Bind.bind, Contracts.requireCustomError, Contracts.revertCustomError, Contracts.formatCustomError, Contracts.requireSomeUintCustomError, String.intercalate, List.intercalate, Pure.pure, Verity.pure, Verity.require, h_owner_raw, h_balance_raw, h_supply_raw,
      Verity.pure, Pure.pure]

-- tama: discharges=erc20_burn_reverts_for_non_owner
theorem burn_reverts_for_non_owner (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_reverts_for_non_owner fromAddr amount s ((burn fromAddr amount).run s) :=
  (burn_properties_after_run fromAddr amount s).1

-- tama: discharges=erc20_burn_reverts_when_balance_is_low
theorem burn_reverts_when_balance_is_low
    (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_reverts_when_balance_is_low fromAddr amount s ((burn fromAddr amount).run s) :=
  (burn_properties_after_run fromAddr amount s).2.1

-- tama: discharges=erc20_burn_reverts_when_total_supply_is_low
theorem burn_reverts_when_total_supply_is_low
    (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_reverts_when_total_supply_is_low fromAddr amount s ((burn fromAddr amount).run s) :=
  (burn_properties_after_run fromAddr amount s).2.2.1

-- tama: discharges=erc20_burn_succeeds_when_owner_has_balance_and_supply
theorem burn_succeeds_when_owner_has_balance_and_supply
    (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_succeeds_when_owner_has_balance_and_supply fromAddr amount s
    ((burn fromAddr amount).run s) :=
  (burn_properties_after_run fromAddr amount s).2.2.2.1

-- tama: discharges=erc20_burn_debits_account
theorem burn_debits_account (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_debits_account fromAddr amount s ((burn fromAddr amount).run s) :=
  (burn_properties_after_run fromAddr amount s).2.2.2.2.1

-- tama: discharges=erc20_burn_decreases_total_supply
theorem burn_decreases_total_supply (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_decreases_total_supply fromAddr amount s ((burn fromAddr amount).run s) :=
  (burn_properties_after_run fromAddr amount s).2.2.2.2.2

end Tamago.Proof.Tokens.ERC20Proof
