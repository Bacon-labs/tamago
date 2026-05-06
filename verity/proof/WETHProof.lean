import spec.WETHSpec
import Verity.Proofs.Stdlib.Automation

namespace proof.WETHProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open spec.WETHSpec
open src.WETH

-- tama: discharges=weth_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  weth_totalSupply_spec ((src.WETH.totalSupply).run s).fst s := by
  simp [weth_totalSupply_spec, src.WETH.totalSupply, totalSupplySlot, Bind.bind, Pure.pure]

-- tama: discharges=weth_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  weth_balanceOf_spec account ((src.WETH.balanceOf account).run s).fst s := by
  simp [weth_balanceOf_spec, src.WETH.balanceOf, balancesSlot, Bind.bind, Pure.pure]

-- tama: discharges=weth_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  weth_allowance_spec ownerAddr spender ((src.WETH.allowance ownerAddr spender).run s).fst s := by
  simp [weth_allowance_spec, src.WETH.allowance, allowancesSlot, Bind.bind, Pure.pure]

-- tama: discharges=weth_approve_effect
theorem approve_updates_allowance_only (spender : Address) (amount : Uint256) (s : ContractState) :
  weth_approve_effect spender amount s ((approve spender amount).run s).snd := by
  unfold weth_approve_effect
  refine ⟨?_, ?_, ?_⟩
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=weth_deposit_effect
theorem deposit_mints_msg_value (s : ContractState) :
  weth_deposit_effect s ((deposit).run s).snd := by
  unfold weth_deposit_effect
  intro h_balance_no_overflow h_supply_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 1 s.sender).val + s.msgValue.val := by omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 0).val + s.msgValue.val := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [deposit, balancesSlot, totalSupplySlot, msgSender, msgValue, getMapping,
      getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_not_balance_overflow, h_not_supply_overflow,
      Verity.pure, Pure.pure]

-- tama: discharges=weth_transfer_total_supply_preserved
theorem transfer_total_supply_preserved_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_total_supply_preserved s ((transfer toAddr amount).run s).snd := by
  unfold weth_transfer_total_supply_preserved
  by_cases h_balance : amount.val ≤ (s.storageMap 1 s.sender).val
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
      Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_balance]
    by_cases h_same : s.sender = toAddr
    · simp [h_same, Verity.pure]
    · by_cases h_overflow : Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 1 toAddr).val + amount.val <;>
        simp [h_same, h_overflow, getMapping, setMapping, Verity.require,
          Verity.bind, Verity.pure]
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_balance]

-- tama: discharges=weth_withdraw_effect
theorem withdraw_burns_before_native_call_on_success (amount : Uint256) (s : ContractState) :
  weth_withdraw_effect amount s ((withdraw amount).run s).snd := by
  unfold weth_withdraw_effect
  intro h_balance h_supply
  refine ⟨?_, ?_⟩ <;>
    simp [withdraw, balancesSlot, totalSupplySlot, msgSender, getMapping, getStorage,
      setMapping, setStorage, Contract.run, ContractResult.snd, Verity.bind,
      Bind.bind, Verity.require, h_balance, h_supply, Verity.pure, Pure.pure]

-- tama: discharges=weth_withdraw_insufficient_no_change
theorem withdraw_insufficient_balance_reverts_without_accounting_change
    (amount : Uint256) (s : ContractState) :
  weth_withdraw_insufficient_no_change amount s ((withdraw amount).run s).snd := by
  unfold weth_withdraw_insufficient_no_change
  intro h_insufficient
  have h_not_balance : ¬ amount.val ≤ (s.storageMap 1 s.sender).val := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [withdraw, balancesSlot, msgSender, getMapping, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_not_balance]

end proof.WETHProof
