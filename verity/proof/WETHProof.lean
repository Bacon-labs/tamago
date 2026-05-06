import spec.WETHSpec
import proof.ERC20Proof
import Verity.Proofs.Stdlib.Automation

namespace proof.WETHProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Contracts
open spec.WETHSpec
open src.WETH

attribute [local simp] tokenSupply balances allowances
attribute [local simp] src.ERC20.tokenSupply src.ERC20.balances src.ERC20.allowances
attribute [local simp] src.ERC20Base.tokenSupply src.ERC20Base.balances
  src.ERC20Base.allowances src.ERC20Base.maxUint256 src.ERC20Base.decimals
  src.ERC20Base.totalSupply src.ERC20Base.balanceOf src.ERC20Base.allowance
  src.ERC20Base.approve src.ERC20Base.transfer src.ERC20Base.transferFrom
attribute [local simp] src.WETHBase.tokenSupply src.WETHBase.balances
  src.WETHBase.allowances src.WETHBase.maxUint256 src.WETHBase.decimals
  src.WETHBase.totalSupply src.WETHBase.balanceOf src.WETHBase.allowance
  src.WETHBase.deposit src.WETHBase.approve src.WETHBase.transfer
  src.WETHBase.transferFrom src.WETHBase.withdraw Contracts.emit emitEvent

-- tama: discharges=weth_decimals_spec
theorem decimals_returns_18 (s : ContractState) :
  weth_decimals_spec ((src.WETH.decimals).run s).fst := by
  simpa [weth_decimals_spec, src.WETH.decimals, src.ERC20.decimals]
    using proof.ERC20Proof.decimals_returns_18 s

-- tama: discharges=weth_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  weth_totalSupply_spec ((src.WETH.totalSupply).run s).fst s := by
  simpa [weth_totalSupply_spec, src.WETH.totalSupply, src.ERC20.totalSupply]
    using proof.ERC20Proof.totalSupply_returns_storage_supply s

-- tama: discharges=weth_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  weth_balanceOf_spec account ((src.WETH.balanceOf account).run s).fst s := by
  simpa [weth_balanceOf_spec, src.WETH.balanceOf, src.ERC20.balanceOf]
    using proof.ERC20Proof.balanceOf_returns_storage_balance account s

-- tama: discharges=weth_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  weth_allowance_spec ownerAddr spender ((src.WETH.allowance ownerAddr spender).run s).fst s := by
  simpa [weth_allowance_spec, src.WETH.allowance, src.ERC20.allowance]
    using proof.ERC20Proof.allowance_returns_storage_allowance ownerAddr spender s

-- tama: discharges=weth_approve_effect
theorem approve_updates_allowance_only (spender : Address) (amount : Uint256) (s : ContractState) :
  weth_approve_effect spender amount s ((src.WETH.approve spender amount).run s) := by
  simpa [weth_approve_effect, src.WETH.approve, src.ERC20.approve]
    using proof.ERC20Proof.approve_updates_allowance_only spender amount s

-- tama: discharges=weth_deposit_effect
theorem deposit_mints_msg_value (s : ContractState) :
  weth_deposit_effect s ((src.WETH.deposit).run s) := by
  unfold weth_deposit_effect
  refine ⟨?_, ?_⟩
  · intro h_balance_overflow
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val := by
      simpa using h_balance_overflow
    simp [src.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
      getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_overflow]
  · intro h_balance_no_overflow
    have h_balance_no_overflow_raw :
        (s.storageMap 2 s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    have h_not_balance_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 s.sender).val + s.msgValue.val := by
      omega
    refine ⟨?_, ?_⟩
    · intro h_supply_overflow
      have h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val := by
        simpa using h_supply_overflow
      simp [src.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
        getStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_not_balance_overflow, h_overflow, Verity.pure, Pure.pure]
    · intro h_supply_no_overflow
      have h_supply_no_overflow_raw :
          (s.storage 1).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_supply_no_overflow
      have h_not_supply_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + s.msgValue.val := by
        omega
      refine ⟨?_, ?_⟩ <;>
        simp [src.WETH.deposit, balances, tokenSupply, msgSender, msgValue, getMapping,
          getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_not_balance_overflow, h_not_supply_overflow,
          Verity.pure, Pure.pure]

-- tama: discharges=weth_transfer_total_supply_preserved
theorem transfer_total_supply_preserved_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_total_supply_preserved s ((src.WETH.transfer toAddr amount).run s).snd := by
  simpa [weth_transfer_total_supply_preserved, src.WETH.transfer, src.ERC20.transfer]
    using proof.ERC20Proof.transfer_total_supply_preserved_after_run toAddr amount s

-- tama: discharges=weth_transfer_balances_effect
theorem transfer_balances_effect_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transfer_balances_effect toAddr amount s ((src.WETH.transfer toAddr amount).run s) := by
  simpa [weth_transfer_balances_effect, src.WETH.transfer, src.ERC20.transfer]
    using proof.ERC20Proof.transfer_balances_effect_after_run toAddr amount s

-- tama: discharges=weth_transferFrom_total_supply_preserved
theorem transferFrom_total_supply_preserved_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_total_supply_preserved s ((src.WETH.transferFrom fromAddr toAddr amount).run s).snd := by
  simpa [weth_transferFrom_total_supply_preserved, src.WETH.transferFrom, src.ERC20.transferFrom]
    using proof.ERC20Proof.transferFrom_total_supply_preserved_after_run fromAddr toAddr amount s

-- tama: discharges=weth_transferFrom_effect
theorem transferFrom_effect_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  weth_transferFrom_effect fromAddr toAddr amount s
    ((src.WETH.transferFrom fromAddr toAddr amount).run s) := by
  simpa [weth_transferFrom_effect, src.WETH.transferFrom, src.ERC20.transferFrom]
    using proof.ERC20Proof.transferFrom_effect_after_run fromAddr toAddr amount s

-- tama: discharges=weth_withdraw_effect
theorem withdraw_burns_wrapped_balance_on_success (amount : Uint256) (s : ContractState) :
  weth_withdraw_effect amount s ((src.WETH.withdraw amount).run s) := by
  unfold weth_withdraw_effect
  refine ⟨?_, ?_⟩
  · intro h_insufficient_balance
    have h_insufficient_balance_raw :
        amount.val > (s.storageMap 2 s.sender).val := by
      simpa using h_insufficient_balance
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 s.sender).val := by omega
    simp [src.WETH.withdraw, balances, tokenSupply, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_not_balance]
  · intro h_balance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    refine ⟨?_, ?_⟩
    · intro h_insufficient_supply
      have h_insufficient_supply_raw : amount.val > (s.storage 1).val := by
        simpa using h_insufficient_supply
      have h_not_supply : ¬ amount.val ≤ (s.storage 1).val := by omega
      simp [src.WETH.withdraw, balances, tokenSupply, msgSender, getMapping, getStorage,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        h_balance_raw, h_not_supply]
    · intro h_supply
      have h_supply_raw : amount.val ≤ (s.storage 1).val := by
          simpa using h_supply
      refine ⟨?_, ?_⟩ <;>
        simp [src.WETH.withdraw, balances, tokenSupply,
          msgSender, getMapping, getStorage, setMapping, setStorage, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance_raw,
          h_supply_raw, Verity.pure, Pure.pure]

end proof.WETHProof
