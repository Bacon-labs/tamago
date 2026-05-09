import Tamago.Spec.Tokens.WETHSpec
import Tamago.Proof.Tokens.ERC20Proof
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Tokens.WETHProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Contracts
open Tamago.Spec.Tokens.WETHSpec
open Tamago.Tokens.WETH

attribute [local simp] tokenSupply balances allowances
attribute [local simp] Tamago.Tokens.ERC20.tokenSupply Tamago.Tokens.ERC20.balances Tamago.Tokens.ERC20.allowances
attribute [local simp] Tamago.Tokens.ERC20Base.tokenSupply Tamago.Tokens.ERC20Base.balances
  Tamago.Tokens.ERC20Base.allowances Tamago.Tokens.ERC20Base.maxUint256 Tamago.Tokens.ERC20Base.decimals
  Tamago.Tokens.ERC20Base.totalSupply Tamago.Tokens.ERC20Base.balanceOf Tamago.Tokens.ERC20Base.allowance
  Tamago.Tokens.ERC20Base.approve Tamago.Tokens.ERC20Base.transfer Tamago.Tokens.ERC20Base.transferFrom
attribute [local simp] Tamago.Tokens.WETHBase.tokenSupply Tamago.Tokens.WETHBase.balances
  Tamago.Tokens.WETHBase.allowances Tamago.Tokens.WETHBase.maxUint256 Tamago.Tokens.WETHBase.decimals
  Tamago.Tokens.WETHBase.totalSupply Tamago.Tokens.WETHBase.balanceOf Tamago.Tokens.WETHBase.allowance
  Tamago.Tokens.WETHBase.deposit Tamago.Tokens.WETHBase.approve Tamago.Tokens.WETHBase.transfer
  Tamago.Tokens.WETHBase.transferFrom Tamago.Tokens.WETHBase.withdraw Contracts.emit emitEvent
attribute [local simp] Tamago.Tokens.WETHNative.transfer

-- tama: discharges=weth_decimals_spec
theorem decimals_returns_18 (s : ContractState) :
  weth_decimals_spec ((Tamago.Tokens.WETH.decimals).run s).fst := by
  simpa [weth_decimals_spec, Tamago.Tokens.WETH.decimals, Tamago.Tokens.ERC20.decimals]
    using Tamago.Proof.Tokens.ERC20Proof.decimals_returns_18 s

-- tama: discharges=weth_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  weth_totalSupply_spec ((Tamago.Tokens.WETH.totalSupply).run s).fst s := by
  simpa [weth_totalSupply_spec, Tamago.Tokens.WETH.totalSupply, Tamago.Tokens.ERC20.totalSupply]
    using Tamago.Proof.Tokens.ERC20Proof.totalSupply_returns_storage_supply s

-- tama: discharges=weth_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  weth_balanceOf_spec account ((Tamago.Tokens.WETH.balanceOf account).run s).fst s := by
  simpa [weth_balanceOf_spec, Tamago.Tokens.WETH.balanceOf, Tamago.Tokens.ERC20.balanceOf]
    using Tamago.Proof.Tokens.ERC20Proof.balanceOf_returns_storage_balance account s

-- tama: discharges=weth_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  weth_allowance_spec ownerAddr spender ((Tamago.Tokens.WETH.allowance ownerAddr spender).run s).fst s := by
  simpa [weth_allowance_spec, Tamago.Tokens.WETH.allowance, Tamago.Tokens.ERC20.allowance]
    using Tamago.Proof.Tokens.ERC20Proof.allowance_returns_storage_allowance ownerAddr spender s

-- tama: discharges=weth_approve_succeeds
theorem approve_succeeds (spender : Address) (amount : Uint256) (s : ContractState) :
  weth_approve_succeeds spender amount s ((Tamago.Tokens.WETH.approve spender amount).run s) := by
  simpa [weth_approve_succeeds, Tamago.Tokens.WETH.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_succeeds spender amount s

-- tama: discharges=weth_approve_sets_allowance
theorem approve_sets_allowance (spender : Address) (amount : Uint256) (s : ContractState) :
  weth_approve_sets_allowance spender amount s ((Tamago.Tokens.WETH.approve spender amount).run s) := by
  simpa [weth_approve_sets_allowance, Tamago.Tokens.WETH.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_sets_allowance spender amount s

-- tama: discharges=weth_approve_keeps_balances
theorem approve_keeps_balances (spender : Address) (amount : Uint256) (s : ContractState) :
  weth_approve_keeps_balances spender amount s ((Tamago.Tokens.WETH.approve spender amount).run s) := by
  simpa [weth_approve_keeps_balances, Tamago.Tokens.WETH.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_keeps_balances spender amount s

-- tama: discharges=weth_approve_keeps_total_supply
theorem approve_keeps_total_supply (spender : Address) (amount : Uint256) (s : ContractState) :
  weth_approve_keeps_total_supply spender amount s ((Tamago.Tokens.WETH.approve spender amount).run s) := by
  simpa [weth_approve_keeps_total_supply, Tamago.Tokens.WETH.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_keeps_total_supply spender amount s

private theorem deposit_properties_after_run (s : ContractState) :
  weth_deposit_reverts_when_sender_balance_would_overflow s ((Tamago.Tokens.WETH.deposit).run s) ∧
  weth_deposit_reverts_when_total_supply_would_overflow s ((Tamago.Tokens.WETH.deposit).run s) ∧
  weth_deposit_succeeds_when_accounting_does_not_overflow s ((Tamago.Tokens.WETH.deposit).run s) ∧
  weth_deposit_credits_sender s ((Tamago.Tokens.WETH.deposit).run s) ∧
  weth_deposit_increases_total_supply s ((Tamago.Tokens.WETH.deposit).run s) ∧
  weth_deposit_preserves_native_backing s ((Tamago.Tokens.WETH.deposit).run s) := by
  unfold weth_deposit_reverts_when_sender_balance_would_overflow
    weth_deposit_reverts_when_total_supply_would_overflow
    weth_deposit_succeeds_when_accounting_does_not_overflow weth_deposit_credits_sender
    weth_deposit_increases_total_supply weth_deposit_preserves_native_backing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_balance_overflow
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val := by
      simpa using h_balance_overflow
    simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
      getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_overflow]
  · intro h_balance_no_overflow h_supply_overflow
    have h_balance_no_overflow_raw :
        (s.storageMap 2 s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    have h_not_balance_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val := by
      omega
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val := by
      simpa using h_supply_overflow
    simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
      getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_not_balance_overflow, h_overflow, Verity.pure, Pure.pure]
  · by_cases h_balance_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val
    · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
        getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_overflow]
    · by_cases h_supply_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val
      · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_balance_overflow, h_supply_overflow, Verity.pure, Pure.pure]
      · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance_overflow, h_supply_overflow,
          Verity.pure, Pure.pure]
  · by_cases h_balance_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val
    · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
        getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_overflow]
    · by_cases h_supply_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val
      · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_balance_overflow, h_supply_overflow, Verity.pure, Pure.pure]
      · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance_overflow, h_supply_overflow,
          Verity.pure, Pure.pure]
  · by_cases h_balance_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val
    · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
        getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_overflow]
    · by_cases h_supply_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val
      · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_balance_overflow, h_supply_overflow, Verity.pure, Pure.pure]
      · simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance_overflow, h_supply_overflow,
          Verity.pure, Pure.pure]
  · intro h_balance_no_overflow h_supply_no_overflow h_backing
    have h_balance_no_overflow_raw :
        (s.storageMap 2 s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa [balances] using h_balance_no_overflow
    have h_supply_no_overflow_raw :
        (s.storage 1).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa [tokenSupply] using h_supply_no_overflow
    have h_not_balance_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val := by
      omega
    have h_not_supply_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val := by
      omega
    have h_supply_lt :
        (s.storage 1).val + s.msgValue.val < 2^256 := by
      have h_supply_max : (s.storage 1).val + s.msgValue.val ≤ 2^256 - 1 := by
        simpa [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] using h_supply_no_overflow_raw
      omega
    have h_supply_add :
        ((s.storage 1) + s.msgValue).val = (s.storage 1).val + s.msgValue.val :=
      Verity.EVM.Uint256.add_eq_of_lt h_supply_lt
    have h_supply_add_rev :
        (s.msgValue + (s.storage 1)).val = (s.storage 1).val + s.msgValue.val := by
      simpa [Verity.Core.Uint256.add_comm] using h_supply_add
    simp [Tamago.Tokens.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
      getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_not_balance_overflow, h_not_supply_overflow,
      h_supply_add, h_supply_add_rev, Verity.pure, Pure.pure]
    exact h_backing

-- tama: discharges=weth_deposit_reverts_when_sender_balance_would_overflow
theorem deposit_reverts_when_sender_balance_would_overflow (s : ContractState) :
  weth_deposit_reverts_when_sender_balance_would_overflow s ((Tamago.Tokens.WETH.deposit).run s) :=
  (deposit_properties_after_run s).1

-- tama: discharges=weth_deposit_reverts_when_total_supply_would_overflow
theorem deposit_reverts_when_total_supply_would_overflow (s : ContractState) :
  weth_deposit_reverts_when_total_supply_would_overflow s ((Tamago.Tokens.WETH.deposit).run s) :=
  (deposit_properties_after_run s).2.1

-- tama: discharges=weth_deposit_succeeds_when_accounting_does_not_overflow
theorem deposit_succeeds_when_accounting_does_not_overflow (s : ContractState) :
  weth_deposit_succeeds_when_accounting_does_not_overflow s ((Tamago.Tokens.WETH.deposit).run s) :=
  (deposit_properties_after_run s).2.2.1

-- tama: discharges=weth_deposit_credits_sender
theorem deposit_credits_sender (s : ContractState) :
  weth_deposit_credits_sender s ((Tamago.Tokens.WETH.deposit).run s) :=
  (deposit_properties_after_run s).2.2.2.1

-- tama: discharges=weth_deposit_increases_total_supply
theorem deposit_increases_total_supply (s : ContractState) :
  weth_deposit_increases_total_supply s ((Tamago.Tokens.WETH.deposit).run s) :=
  (deposit_properties_after_run s).2.2.2.2.1

-- tama: discharges=weth_deposit_preserves_native_backing
theorem deposit_preserves_native_backing (s : ContractState) :
  weth_deposit_preserves_native_backing s ((Tamago.Tokens.WETH.deposit).run s) :=
  (deposit_properties_after_run s).2.2.2.2.2

-- tama: discharges=weth_transfer_reverts_when_balance_is_low
theorem transfer_reverts_when_balance_is_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_reverts_when_balance_is_low toAddr amount s ((Tamago.Tokens.WETH.transfer toAddr amount).run s) := by
  simpa [weth_transfer_reverts_when_balance_is_low, Tamago.Tokens.WETH.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_reverts_when_balance_is_low toAddr amount s

-- tama: discharges=weth_transfer_to_self_keeps_balances
theorem transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_to_self_keeps_balances toAddr amount s ((Tamago.Tokens.WETH.transfer toAddr amount).run s) := by
  simpa [weth_transfer_to_self_keeps_balances, Tamago.Tokens.WETH.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_to_self_keeps_balances toAddr amount s

-- tama: discharges=weth_transfer_reverts_when_recipient_balance_would_overflow
theorem transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s
    ((Tamago.Tokens.WETH.transfer toAddr amount).run s) := by
  simpa [weth_transfer_reverts_when_recipient_balance_would_overflow,
    Tamago.Tokens.WETH.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_reverts_when_recipient_balance_would_overflow toAddr amount s

-- tama: discharges=weth_transfer_moves_tokens_between_distinct_accounts
theorem transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((Tamago.Tokens.WETH.transfer toAddr amount).run s) := by
  simpa [weth_transfer_moves_tokens_between_distinct_accounts,
    Tamago.Tokens.WETH.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_moves_tokens_between_distinct_accounts toAddr amount s

-- tama: discharges=weth_transfer_keeps_total_supply
theorem transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_keeps_total_supply toAddr amount s ((Tamago.Tokens.WETH.transfer toAddr amount).run s) := by
  simpa [weth_transfer_keeps_total_supply, Tamago.Tokens.WETH.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_keeps_total_supply toAddr amount s

-- tama: discharges=weth_transferFrom_reverts_when_allowance_is_low
theorem transferFrom_reverts_when_allowance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_reverts_when_allowance_is_low,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_reverts_when_balance_is_low
theorem transferFrom_reverts_when_balance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_reverts_when_balance_is_low,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_reverts_when_recipient_balance_would_overflow
theorem transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_reverts_when_recipient_balance_would_overflow,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_to_self_keeps_balances
theorem transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_to_self_keeps_balances fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_to_self_keeps_balances,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_to_self_keeps_balances fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_moves_tokens_between_distinct_accounts
theorem transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_moves_tokens_between_distinct_accounts,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_keeps_total_supply
theorem transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_keeps_total_supply fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_keeps_total_supply,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_keeps_total_supply fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_keeps_infinite_allowance
theorem transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_keeps_infinite_allowance,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_keeps_infinite_allowance fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_spends_finite_allowance
theorem transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_spends_finite_allowance fromAddr toAddr amount s
    ((Tamago.Tokens.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_spends_finite_allowance,
    Tamago.Tokens.WETH.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_spends_finite_allowance fromAddr toAddr amount s

private theorem withdraw_properties_after_run (amount : Uint256) (s : ContractState) :
  weth_withdraw_reverts_when_balance_is_low amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_reverts_when_total_supply_is_low amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_reverts_when_eth_backing_is_low amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_reverts_when_native_transfer_fails amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_debits_sender amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_decreases_total_supply amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_decreases_native_balance amount s ((Tamago.Tokens.WETH.withdraw amount).run s) ∧
  weth_withdraw_preserves_native_backing amount s ((Tamago.Tokens.WETH.withdraw amount).run s) := by
  unfold weth_withdraw_reverts_when_balance_is_low
    weth_withdraw_reverts_when_total_supply_is_low weth_withdraw_reverts_when_eth_backing_is_low
    weth_withdraw_reverts_when_native_transfer_fails
    weth_withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough
    weth_withdraw_debits_sender weth_withdraw_decreases_total_supply
    weth_withdraw_decreases_native_balance
    weth_withdraw_preserves_native_backing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_insufficient_balance
    have h_insufficient_balance_raw :
        amount.val > (s.storageMap 2 s.sender).val := by
      simpa using h_insufficient_balance
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 s.sender).val := by omega
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_not_balance]
  · intro h_balance h_insufficient_supply
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_insufficient_supply_raw : amount.val > (s.storage 1).val := by
      simpa using h_insufficient_supply
    have h_not_supply : ¬ amount.val ≤ (s.storage 1).val := by omega
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, getMapping, getStorage,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      h_balance_raw, h_not_supply]
  · intro h_balance h_supply h_insufficient_eth
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_insufficient_eth_raw : amount.val > s.selfBalance.val := by
      simpa using h_insufficient_eth
    have h_not_eth : ¬ amount.val ≤ s.selfBalance.val := by omega
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, Contract.run, ContractResult.snd, Verity.bind,
      Bind.bind, Verity.require, h_balance_raw, h_supply_raw, h_not_eth]
  · intro h_balance h_supply h_eth h_transfer
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_eth_raw : amount.val ≤ s.selfBalance.val := by
      simpa using h_eth
    have h_transfer_raw :
        call 50000 (Verity.Core.Uint256.ofNat (Verity.Core.Address.toNat s.sender)) amount 0 0 0 0 = 0 := by
      simpa [addressToWord] using h_transfer
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, setMapping, setStorage, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
      h_supply_raw, h_eth_raw, h_transfer_raw, Verity.pure, Pure.pure]
  · intro h_balance h_supply h_eth h_transfer
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_eth_raw : amount.val ≤ s.selfBalance.val := by
      simpa using h_eth
    have h_transfer_raw :
        call 50000 (Verity.Core.Uint256.ofNat (Verity.Core.Address.toNat s.sender)) amount 0 0 0 0 ≠ 0 := by
      simpa [addressToWord] using h_transfer
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, setMapping, setStorage, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
      h_supply_raw, h_eth_raw, h_transfer_raw, Verity.pure, Pure.pure]
  · intro h_balance h_supply h_eth h_transfer
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_eth_raw : amount.val ≤ s.selfBalance.val := by
      simpa using h_eth
    have h_transfer_raw :
        call 50000 (Verity.Core.Uint256.ofNat (Verity.Core.Address.toNat s.sender)) amount 0 0 0 0 ≠ 0 := by
      simpa [addressToWord] using h_transfer
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, setMapping, setStorage, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
      h_supply_raw, h_eth_raw, h_transfer_raw, Verity.pure, Pure.pure]
  · intro h_balance h_supply h_eth h_transfer
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_eth_raw : amount.val ≤ s.selfBalance.val := by
      simpa using h_eth
    have h_transfer_raw :
        call 50000 (Verity.Core.Uint256.ofNat (Verity.Core.Address.toNat s.sender)) amount 0 0 0 0 ≠ 0 := by
      simpa [addressToWord] using h_transfer
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, setMapping, setStorage, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
      h_supply_raw, h_eth_raw, h_transfer_raw, Verity.pure, Pure.pure]
  · intro h_balance h_supply h_eth h_transfer
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_eth_raw : amount.val ≤ s.selfBalance.val := by
      simpa using h_eth
    have h_transfer_raw :
        call 50000 (Verity.Core.Uint256.ofNat (Verity.Core.Address.toNat s.sender)) amount 0 0 0 0 ≠ 0 := by
      simpa [addressToWord] using h_transfer
    have h_self_sub :
        (Verity.EVM.Uint256.sub s.selfBalance amount).val =
          s.selfBalance.val - amount.val :=
      Verity.EVM.Uint256.sub_eq_of_le h_eth_raw
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, setMapping, setStorage, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
      h_supply_raw, h_eth_raw, h_transfer_raw, h_self_sub, Verity.pure, Pure.pure]
  · intro h_backing h_balance h_supply h_eth h_transfer
    have h_backing_raw : s.selfBalance.val ≥ (s.storage 1).val := by
      simpa [tokenSupply] using h_backing
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    have h_supply_raw : amount.val ≤ (s.storage 1).val := by
      simpa using h_supply
    have h_eth_raw : amount.val ≤ s.selfBalance.val := by
      simpa using h_eth
    have h_transfer_raw :
        call 50000 (Verity.Core.Uint256.ofNat (Verity.Core.Address.toNat s.sender)) amount 0 0 0 0 ≠ 0 := by
      simpa [addressToWord] using h_transfer
    have h_supply_sub :
        (Verity.EVM.Uint256.sub (s.storage 1) amount).val =
          (s.storage 1).val - amount.val :=
      Verity.EVM.Uint256.sub_eq_of_le h_supply_raw
    have h_self_sub :
        (Verity.EVM.Uint256.sub s.selfBalance amount).val =
          s.selfBalance.val - amount.val :=
      Verity.EVM.Uint256.sub_eq_of_le h_eth_raw
    simp [Tamago.Tokens.WETH.withdraw, balances, tokenSupply, msgSender, selfBalance,
      getMapping, getStorage, setMapping, setStorage, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
      h_supply_raw, h_eth_raw, h_transfer_raw, h_supply_sub, h_self_sub,
      Verity.pure, Pure.pure]
    omega

-- tama: discharges=weth_withdraw_reverts_when_balance_is_low
theorem withdraw_reverts_when_balance_is_low (amount : Uint256) (s : ContractState) :
  weth_withdraw_reverts_when_balance_is_low amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).1

-- tama: discharges=weth_withdraw_reverts_when_total_supply_is_low
theorem withdraw_reverts_when_total_supply_is_low (amount : Uint256) (s : ContractState) :
  weth_withdraw_reverts_when_total_supply_is_low amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.1

-- tama: discharges=weth_withdraw_reverts_when_eth_backing_is_low
theorem withdraw_reverts_when_eth_backing_is_low (amount : Uint256) (s : ContractState) :
  weth_withdraw_reverts_when_eth_backing_is_low amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.1

-- tama: discharges=weth_withdraw_reverts_when_native_transfer_fails
theorem withdraw_reverts_when_native_transfer_fails (amount : Uint256) (s : ContractState) :
  weth_withdraw_reverts_when_native_transfer_fails amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.2.1

-- tama: discharges=weth_withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough
theorem withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough
    (amount : Uint256) (s : ContractState) :
  weth_withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough amount s
    ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.2.2.1

-- tama: discharges=weth_withdraw_debits_sender
theorem withdraw_debits_sender (amount : Uint256) (s : ContractState) :
  weth_withdraw_debits_sender amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.2.2.2.1

-- tama: discharges=weth_withdraw_decreases_total_supply
theorem withdraw_decreases_total_supply (amount : Uint256) (s : ContractState) :
  weth_withdraw_decreases_total_supply amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.2.2.2.2.1

-- tama: discharges=weth_withdraw_decreases_native_balance
theorem withdraw_decreases_native_balance (amount : Uint256) (s : ContractState) :
  weth_withdraw_decreases_native_balance amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.2.2.2.2.2.1

-- tama: discharges=weth_withdraw_preserves_native_backing
theorem withdraw_preserves_native_backing (amount : Uint256) (s : ContractState) :
  weth_withdraw_preserves_native_backing amount s ((Tamago.Tokens.WETH.withdraw amount).run s) :=
  (withdraw_properties_after_run amount s).2.2.2.2.2.2.2.2

end Tamago.Proof.Tokens.WETHProof
