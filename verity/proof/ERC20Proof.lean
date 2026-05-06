import spec.ERC20Spec
import Verity.Proofs.Stdlib.Automation

namespace proof.ERC20Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open spec.ERC20Spec
open src.ERC20

-- tama: discharges=erc20_decimals_spec
theorem decimals_returns_18 (s : ContractState) :
  erc20_decimals_spec ((decimals).run s).fst := by
  simp [erc20_decimals_spec, decimals, Bind.bind, Pure.pure]

-- tama: discharges=erc20_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc20_totalSupply_spec ((totalSupply).run s).fst s := by
  simp [erc20_totalSupply_spec, totalSupply, totalSupplySlot, Bind.bind, Pure.pure]

-- tama: discharges=erc20_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc20_balanceOf_spec account ((balanceOf account).run s).fst s := by
  simp [erc20_balanceOf_spec, balanceOf, balancesSlot, Bind.bind, Pure.pure]

-- tama: discharges=erc20_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  erc20_allowance_spec ownerAddr spender ((allowance ownerAddr spender).run s).fst s := by
  simp [erc20_allowance_spec, allowance, allowancesSlot, Bind.bind, Pure.pure]

-- tama: discharges=erc20_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  erc20_owner_spec ((owner).run s).fst s := by
  simp [erc20_owner_spec, owner, ownerSlot, Bind.bind, Pure.pure]

-- tama: discharges=erc20_approve_effect
theorem approve_updates_allowance_only (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_effect spender amount s ((approve spender amount).run s).snd := by
  unfold erc20_approve_effect
  refine ⟨?_, ?_, ?_⟩
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=erc20_transfer_total_supply_preserved
theorem transfer_total_supply_preserved_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_total_supply_preserved s ((transfer toAddr amount).run s).snd := by
  unfold erc20_transfer_total_supply_preserved
  by_cases h_balance : amount.val ≤ (s.storageMap 2 s.sender).val
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
      Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_balance]
    by_cases h_same : s.sender = toAddr
    · simp [h_same, Verity.pure]
    · by_cases h_overflow : Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val <;>
        simp [h_same, h_overflow, getMapping, setMapping, Verity.require,
          Verity.bind, Verity.pure]
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_balance]

-- tama: discharges=erc20_transfer_balances_effect
theorem transfer_balances_effect_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_balances_effect toAddr amount s ((transfer toAddr amount).run s).snd := by
  unfold erc20_transfer_balances_effect
  intro h_balance
  refine ⟨?_, ?_⟩
  · intro h_eq
    subst h_eq
    simp [transfer, balancesSlot, msgSender, getMapping,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Verity.require, h_balance]
  · intro h_ne h_no_overflow
    have h_not_overflow_strict :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val := by omega
    refine ⟨?_, ?_⟩
    · show ((transfer toAddr amount).run s).snd.storageMap 2 s.sender =
        sub (s.storageMap 2 s.sender) amount
      simp [transfer, balancesSlot, msgSender, getMapping, setMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_balance, h_ne, h_not_overflow_strict]
    · simp [transfer, balancesSlot, msgSender, getMapping, setMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_balance, h_ne, h_not_overflow_strict]

-- tama: discharges=erc20_transferFrom_total_supply_preserved
theorem transferFrom_total_supply_preserved_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_total_supply_preserved s ((transferFrom fromAddr toAddr amount).run s).snd := by
  unfold erc20_transferFrom_total_supply_preserved
  by_cases h_allowance : amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val
  · by_cases h_balance : amount.val ≤ (s.storageMap 2 fromAddr).val
    · simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2, getMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_allowance, h_balance]
      by_cases h_same : fromAddr = toAddr
      · subst h_same
        by_cases h_max :
            s.storageMap2 3 fromAddr s.sender =
              (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Uint256) <;>
          simp [h_max, setMapping2, Verity.pure, Verity.bind]
      · by_cases h_overflow : Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val <;>
          by_cases h_max :
            s.storageMap2 3 fromAddr s.sender =
              (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Uint256) <;>
          simp [h_same, h_overflow, h_max, getMapping, setMapping, setMapping2,
            Verity.require, Verity.bind, Verity.pure]
    · simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2, getMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        h_allowance, h_balance]
  · simp [transferFrom, allowancesSlot, msgSender, getMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      h_allowance]

-- tama: discharges=erc20_transferFrom_allowance_effect
theorem transferFrom_allowance_effect_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_allowance_effect fromAddr toAddr amount s ((transferFrom fromAddr toAddr amount).run s).snd := by
  unfold erc20_transferFrom_allowance_effect
  intro h_allowance h_balance h_no_overflow
  refine ⟨?_, ?_⟩
  · intro h_max
    simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2, getMapping,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
      Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_allowance, h_balance]
    by_cases h_same : fromAddr = toAddr
    · subst h_same
      simp [h_max, Verity.pure]
    · have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val := by
        have h_bound := h_no_overflow h_same
        omega
      simp [h_same, h_not_overflow, h_max, getMapping, setMapping, Verity.require,
        Verity.bind, Verity.pure]
  · intro h_not_max
    simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2, getMapping,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
      Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_allowance, h_balance]
    by_cases h_same : fromAddr = toAddr
    · subst h_same
      simp [h_not_max, setMapping2, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure]
    · have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val := by
        have h_bound := h_no_overflow h_same
        omega
      simp [h_same, h_not_overflow, h_not_max, getMapping, setMapping, setMapping2,
        Verity.require, Verity.bind, Verity.pure]

-- tama: discharges=erc20_mint_effect
theorem mint_effect_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_effect toAddr amount s ((mint toAddr amount).run s).snd := by
  unfold erc20_mint_effect
  intro h_owner h_balance_no_overflow h_supply_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 toAddr).val + amount.val := by omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + amount.val := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, msgSender, getStorageAddr, getMapping,
      getStorage, setMapping, setStorage, Contract.run, ContractResult.snd, Verity.bind,
      Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_not_balance_overflow, h_not_supply_overflow,
      Verity.pure, Pure.pure]
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, msgSender, getStorageAddr, getMapping,
      getStorage, setMapping, setStorage, Contract.run, ContractResult.snd, Verity.bind,
      Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_not_balance_overflow, h_not_supply_overflow,
      Verity.pure, Pure.pure]
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, msgSender, getStorageAddr, getMapping,
      getStorage, setMapping, setStorage, Contract.run, ContractResult.snd, Verity.bind,
      Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_owner, h_not_balance_overflow, h_not_supply_overflow,
      Verity.pure, Pure.pure]

-- tama: discharges=erc20_mint_unauthorized_no_change
theorem mint_unauthorized_no_change_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_unauthorized_no_change toAddr amount s ((mint toAddr amount).run s).snd := by
  unfold erc20_mint_unauthorized_no_change
  intro h_not_owner
  refine ⟨?_, ?_⟩ <;>
    simp [mint, ownerSlot, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_not_owner]

-- tama: discharges=erc20_burn_effect
theorem burn_effect_after_run (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_effect fromAddr amount s ((burn fromAddr amount).run s).snd := by
  unfold erc20_burn_effect
  intro h_owner h_balance h_supply
  refine ⟨?_, ?_⟩ <;>
    simp [burn, ownerSlot, balancesSlot, totalSupplySlot, msgSender, getStorageAddr, getMapping,
      getStorage, setMapping, setStorage, Contract.run, ContractResult.snd, Verity.bind,
      Bind.bind, Verity.require, h_owner, h_balance, h_supply, Verity.pure, Pure.pure]

-- tama: discharges=erc20_burn_unauthorized_no_change
theorem burn_unauthorized_no_change_after_run
    (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_unauthorized_no_change fromAddr amount s ((burn fromAddr amount).run s).snd := by
  unfold erc20_burn_unauthorized_no_change
  intro h_not_owner
  refine ⟨?_, ?_⟩ <;>
    simp [burn, ownerSlot, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_not_owner]

end proof.ERC20Proof
