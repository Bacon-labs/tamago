import spec.ERC20Spec
import proof.OwnableProof
import Verity.Proofs.Stdlib.Automation

namespace proof.ERC20Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open spec.ERC20Spec
open src.ERC20

attribute [local simp] contractOwner tokenSupply balances allowances
  src.ERC20Base.contractOwner src.ERC20Base.tokenSupply src.ERC20Base.balances
  src.ERC20Base.allowances src.ERC20Base.maxUint256
  src.ERC20Base.decimals src.ERC20Base.totalSupply src.ERC20Base.balanceOf
  src.ERC20Base.allowance src.ERC20Base.owner src.ERC20Base.transferOwnership
  src.ERC20Base.renounceOwnership src.ERC20Base.approve src.ERC20Base.transfer
  src.ERC20Base.transferFrom src.ERC20Base.mint src.ERC20Base.burn
  src.OwnableBase.contractOwner src.OwnableBase.transferOwnership
  src.OwnableBase.renounceOwnership Contracts.emit emitEvent

-- tama: discharges=erc20_decimals_spec
theorem decimals_returns_18 (s : ContractState) :
  erc20_decimals_spec ((decimals).run s).fst := by
  simp [erc20_decimals_spec, decimals, Bind.bind, Pure.pure]

-- tama: discharges=erc20_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc20_totalSupply_spec ((totalSupply).run s).fst s := by
  simp [erc20_totalSupply_spec, totalSupply, tokenSupply, Bind.bind, Pure.pure]

-- tama: discharges=erc20_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc20_balanceOf_spec account ((balanceOf account).run s).fst s := by
  simp [erc20_balanceOf_spec, balanceOf, balances, Bind.bind, Pure.pure]

-- tama: discharges=erc20_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  erc20_allowance_spec ownerAddr spender ((allowance ownerAddr spender).run s).fst s := by
  simp [erc20_allowance_spec, allowance, allowances, Bind.bind, Pure.pure]

-- tama: discharges=erc20_owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  erc20_owner_spec ((owner).run s).fst s := by
  simp [erc20_owner_spec, spec.OwnableSpec.ownable_owner_spec, owner, contractOwner,
    src.Ownable.contractOwner, Bind.bind, Pure.pure]

-- tama: discharges=erc20_transferOwnership_effect
theorem transferOwnership_effect_after_run (newOwner : Address) (s : ContractState) :
  erc20_transferOwnership_effect newOwner s ((transferOwnership newOwner).run s) := by
  simpa [erc20_transferOwnership_effect, spec.OwnableSpec.ownable_transferOwnership_effect,
    transferOwnership, src.Ownable.transferOwnership, contractOwner, src.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using proof.OwnableProof.transferOwnership_effect_after_run newOwner s

-- tama: discharges=erc20_renounceOwnership_effect
theorem renounceOwnership_effect_after_run (s : ContractState) :
  erc20_renounceOwnership_effect s ((renounceOwnership).run s) := by
  simpa [erc20_renounceOwnership_effect, spec.OwnableSpec.ownable_renounceOwnership_effect,
    renounceOwnership, src.Ownable.renounceOwnership, contractOwner, src.Ownable.contractOwner,
    Bind.bind, Pure.pure, Verity.bind, Verity.pure]
    using proof.OwnableProof.renounceOwnership_effect_after_run s

-- tama: discharges=erc20_approve_effect
theorem approve_updates_allowance_only (spender : Address) (amount : Uint256) (s : ContractState) :
  erc20_approve_effect spender amount s ((approve spender amount).run s) := by
  unfold erc20_approve_effect
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowances, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=erc20_transfer_total_supply_preserved
theorem transfer_total_supply_preserved_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_total_supply_preserved s ((transfer toAddr amount).run s).snd := by
  unfold erc20_transfer_total_supply_preserved
  by_cases h_balance : amount.val ≤ (s.storageMap 2 s.sender).val
  · simp [transfer, balances, tokenSupply, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
      Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_balance]
    by_cases h_same : s.sender = toAddr
    · simp [h_same, Verity.bind, Bind.bind, Verity.pure, Pure.pure, emitEvent]
    · by_cases h_overflow : Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val
      · simp [h_same, h_overflow, getMapping, setMapping, Verity.require,
          Verity.bind, Verity.pure]
      · simp [h_same, h_overflow, getMapping, setMapping, Verity.require,
          Verity.bind, Verity.pure]
  · simp [transfer, balances, tokenSupply, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance]

-- tama: discharges=erc20_transfer_balances_effect
theorem transfer_balances_effect_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transfer_balances_effect toAddr amount s ((transfer toAddr amount).run s) := by
  unfold erc20_transfer_balances_effect
  refine ⟨?_, ?_⟩
  · intro h_insufficient
    have h_insufficient_raw : amount.val > (s.storageMap 2 s.sender).val := by
      simpa using h_insufficient
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 s.sender).val := by omega
    simp [transfer, balances, msgSender, getMapping, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_not_balance]
  · intro h_balance
    have h_balance_raw : amount.val ≤ (s.storageMap 2 s.sender).val := by
      simpa using h_balance
    refine ⟨?_, ?_⟩
    · intro h_same
      subst h_same
      simp [transfer, balances, msgSender, getMapping, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require, h_balance_raw]
    · intro h_ne
      refine ⟨?_, ?_⟩
      · intro h_overflow
        have h_overflow_strict :
            Verity.Stdlib.Math.MAX_UINT256 <
              (s.storageMap 2 toAddr).val + amount.val := by
          simpa using h_overflow
        simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
          h_overflow_strict]
      · intro h_no_overflow
        have h_no_overflow_raw :
            (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
          simpa using h_no_overflow
        have h_not_overflow :
            ¬ Verity.Stdlib.Math.MAX_UINT256 <
              (s.storageMap 2 toAddr).val + amount.val := by omega
        refine ⟨?_, ?_, ?_⟩
        · simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
            ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
            h_not_overflow]
        · show ((transfer toAddr amount).run s).snd.storageMap 2 s.sender =
            sub (s.storageMap 2 s.sender) amount
          simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
            ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
            h_not_overflow]
        · simp [transfer, balances, msgSender, getMapping, setMapping, Contract.run,
            ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne,
            h_not_overflow, HSub.hSub]

-- tama: discharges=erc20_transferFrom_total_supply_preserved
theorem transferFrom_total_supply_preserved_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_total_supply_preserved s ((transferFrom fromAddr toAddr amount).run s).snd := by
  unfold erc20_transferFrom_total_supply_preserved
  by_cases h_allowance : amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val
  · by_cases h_balance : amount.val ≤ (s.storageMap 2 fromAddr).val
    · simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
        getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure,
        Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_allowance, h_balance]
      by_cases h_same : fromAddr = toAddr
      · subst h_same
        by_cases h_max :
            s.storageMap2 3 fromAddr s.sender =
              maxUint256
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          simp [h_max, setMapping2, Verity.pure, Verity.bind]
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          simp [h_max, setMapping2, Verity.pure, Verity.bind]
      · by_cases h_overflow : Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val
        · by_cases h_max :
              s.storageMap2 3 fromAddr s.sender =
                maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [h_same, h_overflow, h_max, getMapping, setMapping, setMapping2,
              Verity.require, Verity.bind, Verity.pure]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [h_same, h_overflow, h_max, getMapping, setMapping, setMapping2,
              Verity.require, Verity.bind, Verity.pure]
        · by_cases h_max :
              s.storageMap2 3 fromAddr s.sender =
                maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [h_same, h_overflow, h_max, getMapping, setMapping, setMapping2,
              Verity.require, Verity.bind, Verity.pure]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [h_same, h_overflow, h_max, getMapping, setMapping, setMapping2,
              Verity.require, Verity.bind, Verity.pure]
    · simp [transferFrom, allowances, balances, tokenSupply, msgSender, getMapping2,
        getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        h_allowance, h_balance]
  · simp [transferFrom, allowances, tokenSupply, msgSender, getMapping2,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_allowance]

-- tama: discharges=erc20_transferFrom_effect
theorem transferFrom_effect_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_transferFrom_effect fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) := by
  unfold erc20_transferFrom_effect
  refine ⟨?_, ?_⟩
  · intro h_insufficient_allowance
    have h_insufficient_allowance_raw :
        amount.val > (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_insufficient_allowance
    have h_not_allowance :
        ¬ amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by omega
    simp [transferFrom, allowances, msgSender, getMapping2, Contract.run, Verity.bind,
      Bind.bind, Verity.require, h_not_allowance]
  · intro h_allowance
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val := by
      simpa using h_allowance
    refine ⟨?_, ?_⟩
    · intro h_insufficient_balance
      have h_insufficient_balance_raw :
          amount.val > (s.storageMap 2 fromAddr).val := by
        simpa using h_insufficient_balance
      have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 fromAddr).val := by omega
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        Contract.run, Verity.bind, Bind.bind, Verity.require, h_allowance_raw, h_not_balance]
    · intro h_balance
      have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
        simpa using h_balance
      simp [transferFrom, allowances, balances, msgSender, getMapping2, getMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_allowance_raw, h_balance_raw]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h_ne
        refine ⟨?_, ?_⟩
        · intro h_overflow
          have h_overflow_strict :
              Verity.Stdlib.Math.MAX_UINT256 <
                (s.storageMap 2 toAddr).val + amount.val := by
            simpa using h_overflow
          simp [h_ne, h_overflow_strict, getMapping, setMapping, Verity.require,
            Verity.bind, Verity.pure]
        · intro h_no_overflow
          have h_no_overflow_raw :
              (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
            simpa using h_no_overflow
          have h_not_overflow :
              ¬ Verity.Stdlib.Math.MAX_UINT256 <
                (s.storageMap 2 toAddr).val + amount.val := by omega
          by_cases h_max :
              s.storageMap2 3 fromAddr s.sender =
                maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            refine ⟨?_, ?_, ?_⟩ <;>
              simp [h_ne, h_not_overflow, h_max, getMapping, setMapping, setMapping2,
                Verity.require, Verity.bind, Verity.pure, HSub.hSub]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            refine ⟨?_, ?_, ?_⟩ <;>
              simp [h_ne, h_not_overflow, h_max, getMapping, setMapping, setMapping2,
                Verity.require, Verity.bind, Verity.pure, HSub.hSub]
      · intro h_eq
        subst h_eq
        by_cases h_max :
            s.storageMap2 3 fromAddr s.sender =
              maxUint256
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          simp [h_max, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
            Bind.bind, Verity.pure, Pure.pure]
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          simp [h_max, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
            Bind.bind, Verity.pure, Pure.pure]
      · intro h_path h_max
        have h_max_ofNat :
            s.storageMap2 3 fromAddr s.sender =
              maxUint256 := by
          change s.storageMap2 3 fromAddr s.sender =
            maxUint256
          simpa using h_max
        simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max_ofNat
        by_cases h_same : fromAddr = toAddr
        · subst h_same
          simp [h_max_ofNat, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
            Pure.pure, emitEvent]
        · have h_not_overflow :
              ¬ Verity.Stdlib.Math.MAX_UINT256 <
                (s.storageMap 2 toAddr).val + amount.val := by
            rcases h_path with h_eq | h_no_overflow
            · exact False.elim (h_same h_eq)
            · have h_no_overflow_raw :
                  (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
                simpa using h_no_overflow
              omega
          simp [h_same, h_not_overflow, h_max_ofNat, getMapping, setMapping, Verity.require,
            Verity.bind, Verity.pure]
      · intro h_path h_not_max
        have h_not_max_ofNat :
            s.storageMap2 3 fromAddr s.sender ≠
              maxUint256 := by
          change s.storageMap2 3 fromAddr s.sender ≠
            maxUint256
          simpa using h_not_max
        simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_not_max_ofNat
        by_cases h_same : fromAddr = toAddr
        · subst h_same
          simp [h_not_max_ofNat, setMapping2, Contract.run, ContractResult.snd,
            Verity.bind, Bind.bind, Verity.pure, Pure.pure]
        · have h_not_overflow :
              ¬ Verity.Stdlib.Math.MAX_UINT256 <
                (s.storageMap 2 toAddr).val + amount.val := by
            rcases h_path with h_eq | h_no_overflow
            · exact False.elim (h_same h_eq)
            · have h_no_overflow_raw :
                  (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
                simpa using h_no_overflow
              omega
          simp [h_same, h_not_overflow, h_not_max_ofNat, getMapping, setMapping, setMapping2,
            Verity.require, Verity.bind, Verity.pure]

-- tama: discharges=erc20_mint_effect
theorem mint_effect_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_mint_effect toAddr amount s ((mint toAddr amount).run s) := by
  unfold erc20_mint_effect
  refine ⟨?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa using h_not_owner
    simp [mint, contractOwner, msgSender, getStorageAddr, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_not_owner_raw]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    refine ⟨?_, ?_⟩
    · intro h_balance_overflow
      have h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val := by
        simpa using h_balance_overflow
      simp [mint, contractOwner, balances, msgSender, getStorageAddr, getMapping,
        Contract.run, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw, h_overflow]
    · intro h_balance_no_overflow
      have h_balance_no_overflow_raw :
          (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_balance_no_overflow
      have h_not_balance_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val := by omega
      refine ⟨?_, ?_⟩
      · intro h_supply_overflow
        have h_overflow :
            Verity.Stdlib.Math.MAX_UINT256 <
              (s.storage 1).val + amount.val := by
          simpa using h_supply_overflow
        simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
          getMapping, getStorage, Contract.run, Verity.bind, Bind.bind, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner_raw,
          h_not_balance_overflow, h_overflow, ContractResult.snd, Verity.pure, Pure.pure]
      · intro h_supply_no_overflow
        have h_supply_no_overflow_raw :
            (s.storage 1).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
          simpa using h_supply_no_overflow
        have h_not_supply_overflow :
            ¬ Verity.Stdlib.Math.MAX_UINT256 <
              (s.storage 1).val + amount.val := by omega
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [mint, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
            Verity.bind, Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_owner_raw, h_not_balance_overflow,
            h_not_supply_overflow, Verity.pure, Pure.pure]

-- tama: discharges=erc20_burn_effect
theorem burn_effect_after_run (fromAddr : Address) (amount : Uint256) (s : ContractState) :
  erc20_burn_effect fromAddr amount s ((burn fromAddr amount).run s) := by
  unfold erc20_burn_effect
  refine ⟨?_, ?_⟩
  · intro h_not_owner
    have h_not_owner_raw : s.sender ≠ s.storageAddr 0 := by
      simpa using h_not_owner
    simp [burn, contractOwner, msgSender, getStorageAddr, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_not_owner_raw]
  · intro h_owner
    have h_owner_raw : s.sender = s.storageAddr 0 := by
      simpa using h_owner
    refine ⟨?_, ?_⟩
    · intro h_insufficient_balance
      have h_insufficient_balance_raw :
          amount.val > (s.storageMap 2 fromAddr).val := by
        simpa using h_insufficient_balance
      have h_not_balance : ¬ amount.val ≤ (s.storageMap 2 fromAddr).val := by omega
      simp [burn, contractOwner, balances, msgSender, getStorageAddr, getMapping,
        Contract.run, Verity.bind, Bind.bind, Verity.require, h_owner_raw, h_not_balance]
    · intro h_balance
      have h_balance_raw : amount.val ≤ (s.storageMap 2 fromAddr).val := by
        simpa using h_balance
      refine ⟨?_, ?_⟩
      · intro h_insufficient_supply
        have h_insufficient_supply_raw :
            amount.val > (s.storage 1).val := by
          simpa using h_insufficient_supply
        have h_not_supply : ¬ amount.val ≤ (s.storage 1).val := by omega
        simp [burn, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
          getMapping, getStorage, Contract.run, Verity.bind, Bind.bind, Verity.require,
          h_owner_raw, h_balance_raw, h_not_supply]
      · intro h_supply
        have h_supply_raw : amount.val ≤ (s.storage 1).val := by
          simpa using h_supply
        refine ⟨?_, ?_, ?_⟩ <;>
          simp [burn, contractOwner, balances, tokenSupply, msgSender, getStorageAddr,
            getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
            Verity.bind, Bind.bind, Verity.require, h_owner_raw, h_balance_raw, h_supply_raw,
            Verity.pure, Pure.pure]

end proof.ERC20Proof
