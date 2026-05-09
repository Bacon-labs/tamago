import Tamago.Spec.Tokens.ERC4626Spec
import Tamago.Proof.Tokens.ERC20Proof
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Tokens.ERC4626Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Contracts
open Tamago.Spec.Tokens.ERC4626Spec
open Tamago.Tokens.ERC4626
open Tamago.Common.ERC4626Concrete
open Tamago.Common.ERC4626Ghost

attribute [local simp] assetToken tokenSupply balances allowances managedAssets
attribute [local simp] Tamago.Tokens.ERC20.tokenSupply Tamago.Tokens.ERC20.balances Tamago.Tokens.ERC20.allowances
attribute [local simp] Tamago.Tokens.ERC20Base.tokenSupply Tamago.Tokens.ERC20Base.balances
  Tamago.Tokens.ERC20Base.allowances Tamago.Tokens.ERC20Base.maxUint256 Tamago.Tokens.ERC20Base.decimals
  Tamago.Tokens.ERC20Base.totalSupply Tamago.Tokens.ERC20Base.balanceOf Tamago.Tokens.ERC20Base.allowance
  Tamago.Tokens.ERC20Base.approve Tamago.Tokens.ERC20Base.transfer Tamago.Tokens.ERC20Base.transferFrom
attribute [local simp] Tamago.Tokens.ERC4626Base.__verity_immutable_slot_assetToken
  Tamago.Tokens.ERC4626Base.tokenSupply
  Tamago.Tokens.ERC4626Base.balances Tamago.Tokens.ERC4626Base.allowances Tamago.Tokens.ERC4626Base.managedAssets
  Tamago.Tokens.ERC4626Base.maxUint256 Tamago.Tokens.ERC4626Base.decimals Tamago.Tokens.ERC4626Base.totalSupply
  Tamago.Tokens.ERC4626Base.balanceOf Tamago.Tokens.ERC4626Base.allowance Tamago.Tokens.ERC4626Base.approve
  Tamago.Tokens.ERC4626Base.transfer Tamago.Tokens.ERC4626Base.transferFrom Tamago.Tokens.ERC4626Base.asset
  Tamago.Tokens.ERC4626Base.totalAssets Tamago.Tokens.ERC4626Base.convertToShares
  Tamago.Tokens.ERC4626Base.convertToAssets Tamago.Tokens.ERC4626Base.maxDeposit Tamago.Tokens.ERC4626Base.maxMint
  Tamago.Tokens.ERC4626Base.maxWithdraw Tamago.Tokens.ERC4626Base.maxRedeem Tamago.Tokens.ERC4626Base.previewDeposit
  Tamago.Tokens.ERC4626Base.previewMint Tamago.Tokens.ERC4626Base.previewWithdraw Tamago.Tokens.ERC4626Base.previewRedeem
  Tamago.Tokens.ERC4626Base.deposit Tamago.Tokens.ERC4626Base.mint Tamago.Tokens.ERC4626Base.withdraw
  Tamago.Tokens.ERC4626Base.redeem Contracts.emit emitEvent
attribute [local simp] Tamago.Tokens.safeTransfer Tamago.Tokens.safeTransferFrom
  Tamago.Tokens.traceERC4626AssetSafeTransfer Tamago.Tokens.traceERC4626AssetSafeTransferFrom
  Tamago.Tokens.erc4626AssetSafeTransferEvent Tamago.Tokens.erc4626AssetSafeTransferFromEvent
  Tamago.Tokens.ERC4626Runtime.selfAddress Verity.contractAddress

-- tama: discharges=erc4626_decimals_spec
theorem decimals_returns_18 (s : ContractState) :
  erc4626_decimals_spec ((Tamago.Tokens.ERC4626.decimals).run s).fst := by
  simpa [erc4626_decimals_spec, Tamago.Tokens.ERC4626.decimals, Tamago.Tokens.ERC20.decimals]
    using Tamago.Proof.Tokens.ERC20Proof.decimals_returns_18 s

-- tama: discharges=erc4626_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc4626_totalSupply_spec ((Tamago.Tokens.ERC4626.totalSupply).run s).fst s := by
  simpa [erc4626_totalSupply_spec, Tamago.Tokens.ERC4626.totalSupply, Tamago.Tokens.ERC20.totalSupply]
    using Tamago.Proof.Tokens.ERC20Proof.totalSupply_returns_storage_supply s

-- tama: discharges=erc4626_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc4626_balanceOf_spec account ((Tamago.Tokens.ERC4626.balanceOf account).run s).fst s := by
  simpa [erc4626_balanceOf_spec, Tamago.Tokens.ERC4626.balanceOf, Tamago.Tokens.ERC20.balanceOf]
    using Tamago.Proof.Tokens.ERC20Proof.balanceOf_returns_storage_balance account s

-- tama: discharges=erc4626_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  erc4626_allowance_spec ownerAddr spender ((Tamago.Tokens.ERC4626.allowance ownerAddr spender).run s).fst s := by
  simpa [erc4626_allowance_spec, Tamago.Tokens.ERC4626.allowance, Tamago.Tokens.ERC20.allowance]
    using Tamago.Proof.Tokens.ERC20Proof.allowance_returns_storage_allowance ownerAddr spender s

-- tama: discharges=erc4626_approve_succeeds
theorem approve_succeeds (spender : Address) (amount : Uint256) (s : ContractState) :
  erc4626_approve_succeeds spender amount s ((Tamago.Tokens.ERC4626.approve spender amount).run s) := by
  simpa [erc4626_approve_succeeds, Tamago.Tokens.ERC4626.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_succeeds spender amount s

-- tama: discharges=erc4626_approve_sets_allowance
theorem approve_sets_allowance (spender : Address) (amount : Uint256) (s : ContractState) :
  erc4626_approve_sets_allowance spender amount s ((Tamago.Tokens.ERC4626.approve spender amount).run s) := by
  simpa [erc4626_approve_sets_allowance, Tamago.Tokens.ERC4626.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_sets_allowance spender amount s

-- tama: discharges=erc4626_approve_keeps_balances
theorem approve_keeps_balances (spender : Address) (amount : Uint256) (s : ContractState) :
  erc4626_approve_keeps_balances spender amount s ((Tamago.Tokens.ERC4626.approve spender amount).run s) := by
  simpa [erc4626_approve_keeps_balances, Tamago.Tokens.ERC4626.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_keeps_balances spender amount s

-- tama: discharges=erc4626_approve_keeps_total_supply
theorem approve_keeps_total_supply (spender : Address) (amount : Uint256) (s : ContractState) :
  erc4626_approve_keeps_total_supply spender amount s ((Tamago.Tokens.ERC4626.approve spender amount).run s) := by
  simpa [erc4626_approve_keeps_total_supply, Tamago.Tokens.ERC4626.approve, Tamago.Tokens.ERC20.approve]
    using Tamago.Proof.Tokens.ERC20Proof.approve_keeps_total_supply spender amount s

-- tama: discharges=erc4626_transfer_reverts_when_balance_is_low
theorem transfer_reverts_when_balance_is_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_reverts_when_balance_is_low toAddr amount s ((Tamago.Tokens.ERC4626.transfer toAddr amount).run s) := by
  simpa [erc4626_transfer_reverts_when_balance_is_low, Tamago.Tokens.ERC4626.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_reverts_when_balance_is_low toAddr amount s

-- tama: discharges=erc4626_transfer_to_self_keeps_balances
theorem transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_to_self_keeps_balances toAddr amount s ((Tamago.Tokens.ERC4626.transfer toAddr amount).run s) := by
  simpa [erc4626_transfer_to_self_keeps_balances, Tamago.Tokens.ERC4626.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_to_self_keeps_balances toAddr amount s

-- tama: discharges=erc4626_transfer_reverts_when_recipient_balance_would_overflow
theorem transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s
    ((Tamago.Tokens.ERC4626.transfer toAddr amount).run s) := by
  simpa [erc4626_transfer_reverts_when_recipient_balance_would_overflow,
    Tamago.Tokens.ERC4626.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_reverts_when_recipient_balance_would_overflow toAddr amount s

-- tama: discharges=erc4626_transfer_moves_tokens_between_distinct_accounts
theorem transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((Tamago.Tokens.ERC4626.transfer toAddr amount).run s) := by
  simpa [erc4626_transfer_moves_tokens_between_distinct_accounts,
    Tamago.Tokens.ERC4626.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_moves_tokens_between_distinct_accounts toAddr amount s

-- tama: discharges=erc4626_transfer_keeps_total_supply
theorem transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_keeps_total_supply toAddr amount s ((Tamago.Tokens.ERC4626.transfer toAddr amount).run s) := by
  simpa [erc4626_transfer_keeps_total_supply, Tamago.Tokens.ERC4626.transfer, Tamago.Tokens.ERC20.transfer]
    using Tamago.Proof.Tokens.ERC20Proof.transfer_keeps_total_supply toAddr amount s

-- tama: discharges=erc4626_transferFrom_reverts_when_allowance_is_low
theorem transferFrom_reverts_when_allowance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_reverts_when_allowance_is_low,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_reverts_when_balance_is_low
theorem transferFrom_reverts_when_balance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_reverts_when_balance_is_low,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_reverts_when_recipient_balance_would_overflow
theorem transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_reverts_when_recipient_balance_would_overflow,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_to_self_keeps_balances
theorem transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_to_self_keeps_balances fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_to_self_keeps_balances,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_to_self_keeps_balances fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_moves_tokens_between_distinct_accounts
theorem transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_moves_tokens_between_distinct_accounts,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_keeps_total_supply
theorem transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_keeps_total_supply fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_keeps_total_supply,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_keeps_total_supply fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_keeps_infinite_allowance
theorem transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_keeps_infinite_allowance,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_keeps_infinite_allowance fromAddr toAddr amount s

-- tama: discharges=erc4626_transferFrom_spends_finite_allowance
theorem transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_spends_finite_allowance fromAddr toAddr amount s
    ((Tamago.Tokens.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_spends_finite_allowance,
    Tamago.Tokens.ERC4626.transferFrom, Tamago.Tokens.ERC20.transferFrom]
    using Tamago.Proof.Tokens.ERC20Proof.transferFrom_spends_finite_allowance fromAddr toAddr amount s

-- tama: discharges=erc4626_asset_spec
theorem asset_returns_storage_asset (s : ContractState) :
  erc4626_asset_spec ((asset).run s).fst s := by
  simp [erc4626_asset_spec, asset, assetToken, getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_totalAssets_spec
theorem totalAssets_returns_managed_assets (s : ContractState) :
  erc4626_totalAssets_spec ((totalAssets).run s).fst s := by
  simp [erc4626_totalAssets_spec, totalAssets, managedAssets, getStorageAddr,
    getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure,
    Bind.bind, Pure.pure]

-- tama: discharges=erc4626_convertToShares_spec
theorem convertToShares_uses_virtual_share_formula (assets : Uint256) (s : ContractState) :
  erc4626_convertToShares_spec assets ((convertToShares assets).run s).fst s := by
  simp [erc4626_convertToShares_spec, convertToShares, managedAssets, tokenSupply,
    getStorageAddr, getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_convertToAssets_spec
theorem convertToAssets_uses_virtual_share_formula (shares : Uint256) (s : ContractState) :
  erc4626_convertToAssets_spec shares ((convertToAssets shares).run s).fst s := by
  simp [erc4626_convertToAssets_spec, convertToAssets, managedAssets, tokenSupply,
    getStorageAddr, getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxDeposit_spec
theorem maxDeposit_returns_max_uint256 (receiver : Address) (s : ContractState) :
  erc4626_maxDeposit_spec receiver ((maxDeposit receiver).run s).fst := by
  simp [erc4626_maxDeposit_spec, maxDeposit, maxUint256, getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxMint_spec
theorem maxMint_returns_max_uint256 (receiver : Address) (s : ContractState) :
  erc4626_maxMint_spec receiver ((maxMint receiver).run s).fst := by
  simp [erc4626_maxMint_spec, maxMint, maxUint256, getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxWithdraw_spec
theorem maxWithdraw_returns_convertible_owner_assets (ownerAddr : Address) (s : ContractState) :
  erc4626_maxWithdraw_spec ownerAddr ((maxWithdraw ownerAddr).run s).fst s := by
  simp [erc4626_maxWithdraw_spec, maxWithdraw, managedAssets, tokenSupply, balances,
    getStorageAddr, getMapping, getStorage, Contract.run, Verity.bind, Verity.pure,
    Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxRedeem_spec
theorem maxRedeem_returns_owner_shares (ownerAddr : Address) (s : ContractState) :
  erc4626_maxRedeem_spec ownerAddr ((maxRedeem ownerAddr).run s).fst s := by
  simp [erc4626_maxRedeem_spec, maxRedeem, balances, getStorageAddr, getMapping,
    Contract.run, ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewDeposit_spec
theorem previewDeposit_matches_convertToShares (assets : Uint256) (s : ContractState) :
  erc4626_previewDeposit_spec assets ((previewDeposit assets).run s).fst s := by
  simp [erc4626_previewDeposit_spec, erc4626_convertToShares_spec, previewDeposit,
    convertToShares, managedAssets, tokenSupply, getStorageAddr, getStorage, Contract.run, Verity.bind,
    Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewMint_spec
theorem previewMint_rounds_assets_up (shares : Uint256) (s : ContractState) :
  erc4626_previewMint_spec shares ((previewMint shares).run s).fst s := by
  simp [erc4626_previewMint_spec, previewMint, managedAssets, tokenSupply, getStorageAddr,
    getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewWithdraw_spec
theorem previewWithdraw_rounds_shares_up (assets : Uint256) (s : ContractState) :
  erc4626_previewWithdraw_spec assets ((previewWithdraw assets).run s).fst s := by
  simp [erc4626_previewWithdraw_spec, previewWithdraw, managedAssets, tokenSupply, getStorageAddr,
    getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewRedeem_spec
theorem previewRedeem_matches_convertToAssets (shares : Uint256) (s : ContractState) :
  erc4626_previewRedeem_spec shares ((previewRedeem shares).run s).fst s := by
  simp [erc4626_previewRedeem_spec, erc4626_convertToAssets_spec, previewRedeem,
    convertToAssets, managedAssets, tokenSupply, getStorageAddr, getStorage, Contract.run, Verity.bind,
    Verity.pure, Bind.bind, Pure.pure]

private theorem deposit_properties_after_run
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  ((s.storageMap balances.slot receiver).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
    (deposit assets receiver).run s = ContractResult.revert "Balance overflow" s) ∧
  ((s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    ((s.storage tokenSupply.slot).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
      (deposit assets receiver).run s = ContractResult.revert "Supply overflow" s) ∧
    ((s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      ((s.storage managedAssets.slot).val + assets.val > Verity.Stdlib.Math.MAX_UINT256 →
        (deposit assets receiver).run s = ContractResult.revert "Total assets overflow" s) ∧
      ((s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        (deposit assets receiver).run s = ContractResult.success shares ((deposit assets receiver).run s).snd ∧
        ((deposit assets receiver).run s).snd.storageMap balances.slot receiver =
          (s.storageMap balances.slot receiver) + shares ∧
        ((deposit assets receiver).run s).snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + shares ∧
        ((deposit assets receiver).run s).snd.storage managedAssets.slot =
          (s.storage managedAssets.slot) + assets ∧
            ((deposit assets receiver).run s).snd.storageAddr assetToken.slot = s.storageAddr assetToken.slot))) := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro h_balance_overflow
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 receiver).val +
            (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
      simpa using h_balance_overflow
    simp [deposit, assetToken, balances, tokenSupply, managedAssets, msgSender,
      getStorageAddr, getStorage, getMapping, safeTransferFrom,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_overflow,
      Verity.pure, Pure.pure]
  · intro h_balance_no_overflow
    have h_balance_no_overflow_raw :
        (s.storageMap 2 receiver).val +
            (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    have h_not_balance_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 receiver).val +
            (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
      omega
    refine ⟨?_, ?_⟩
    · intro h_supply_overflow
      have h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 <
            (s.storage 1).val +
              (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
        simpa using h_supply_overflow
      simp [deposit, assetToken, balances, tokenSupply, managedAssets, msgSender,
        getStorageAddr, getStorage, getMapping, safeTransferFrom,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_not_balance_overflow, h_overflow, Verity.pure, Pure.pure]
    · intro h_supply_no_overflow
      have h_supply_no_overflow_raw :
          (s.storage 1).val +
              (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val ≤
            Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_supply_no_overflow
      have h_not_supply_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storage 1).val +
              (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
        omega
      refine ⟨?_, ?_⟩
      · intro h_assets_overflow
        have h_overflow :
            Verity.Stdlib.Math.MAX_UINT256 < (s.storage 4).val + assets.val := by
          simpa using h_assets_overflow
        simp [deposit, assetToken, balances, tokenSupply, managedAssets, msgSender,
          getStorageAddr, getStorage, getMapping, setMapping,
          setStorage, safeTransferFrom, Contract.run, ContractResult.snd, Verity.bind,
          Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_not_balance_overflow, h_not_supply_overflow,
          h_overflow, Verity.pure, Pure.pure]
      · intro h_assets_no_overflow
        have h_assets_no_overflow_raw :
            (s.storage 4).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
          simpa using h_assets_no_overflow
        have h_not_assets_overflow :
            ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 4).val + assets.val := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [deposit, assetToken, balances, tokenSupply, managedAssets, msgSender,
            getStorageAddr, getStorage, getMapping, setMapping,
            setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
            Verity.pure, Pure.pure]

-- tama: discharges=erc4626_deposit_reverts_when_receiver_balance_would_overflow
theorem deposit_reverts_when_receiver_balance_would_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_reverts_when_receiver_balance_would_overflow assets receiver s
    ((deposit assets receiver).run s) :=
  (deposit_properties_after_run assets receiver s).1

-- tama: discharges=erc4626_deposit_reverts_when_total_supply_would_overflow
theorem deposit_reverts_when_total_supply_would_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_reverts_when_total_supply_would_overflow assets receiver s
    ((deposit assets receiver).run s) :=
  fun h_balance h_supply => ((deposit_properties_after_run assets receiver s).2 h_balance).1 h_supply

-- tama: discharges=erc4626_deposit_reverts_when_total_assets_would_overflow
theorem deposit_reverts_when_total_assets_would_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_reverts_when_total_assets_would_overflow assets receiver s
    ((deposit assets receiver).run s) :=
  fun h_balance h_supply h_assets =>
    (((deposit_properties_after_run assets receiver s).2 h_balance).2 h_supply).1 h_assets

-- tama: discharges=erc4626_deposit_succeeds_when_accounting_does_not_overflow
theorem deposit_succeeds_when_accounting_does_not_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_succeeds_when_accounting_does_not_overflow assets receiver s
    ((deposit assets receiver).run s) :=
  fun h_balance h_supply h_assets =>
    ((((deposit_properties_after_run assets receiver s).2 h_balance).2 h_supply).2 h_assets).1

-- tama: discharges=erc4626_deposit_credits_receiver
theorem deposit_credits_receiver
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_credits_receiver assets receiver s ((deposit assets receiver).run s) :=
  fun h_balance h_supply h_assets =>
    ((((deposit_properties_after_run assets receiver s).2 h_balance).2 h_supply).2 h_assets).2.1

-- tama: discharges=erc4626_deposit_increases_total_supply
theorem deposit_increases_total_supply
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_increases_total_supply assets receiver s ((deposit assets receiver).run s) :=
  fun h_balance h_supply h_assets =>
    ((((deposit_properties_after_run assets receiver s).2 h_balance).2 h_supply).2 h_assets).2.2.1

-- tama: discharges=erc4626_deposit_increases_total_assets
theorem deposit_increases_total_assets
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_increases_total_assets assets receiver s ((deposit assets receiver).run s) :=
  fun h_balance h_supply h_assets =>
    ((((deposit_properties_after_run assets receiver s).2 h_balance).2 h_supply).2 h_assets).2.2.2.1

-- tama: discharges=erc4626_deposit_keeps_asset
theorem deposit_keeps_asset
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_keeps_asset assets receiver s ((deposit assets receiver).run s) :=
  fun h_balance h_supply h_assets =>
    ((((deposit_properties_after_run assets receiver s).2 h_balance).2 h_supply).2 h_assets).2.2.2.2

-- tama: discharges=erc4626_mint_reverts_when_receiver_balance_would_overflow
theorem mint_reverts_when_receiver_balance_would_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_reverts_when_receiver_balance_would_overflow shares receiver s
    ((mint shares receiver).run s) := by
  unfold erc4626_mint_reverts_when_receiver_balance_would_overflow
  intro h_balance_overflow
  have h_overflow :
      Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    simpa using h_balance_overflow
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_overflow,
    Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_reverts_when_total_supply_would_overflow
theorem mint_reverts_when_total_supply_would_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_reverts_when_total_supply_would_overflow shares receiver s
    ((mint shares receiver).run s) := by
  unfold erc4626_mint_reverts_when_total_supply_would_overflow
  intro h_balance_no_overflow h_supply_overflow
  have h_balance_no_overflow_raw :
      (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
    simpa using h_balance_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    omega
  have h_overflow :
      Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
    simpa using h_supply_overflow
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    h_not_balance_overflow, h_overflow, Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_reverts_when_total_assets_would_overflow
theorem mint_reverts_when_total_assets_would_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_reverts_when_total_assets_would_overflow shares receiver s
    ((mint shares receiver).run s) := by
  unfold erc4626_mint_reverts_when_total_assets_would_overflow
  dsimp
  intro h_balance_no_overflow h_supply_no_overflow h_assets_overflow
  have h_balance_no_overflow_raw :
      (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
    simpa using h_balance_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    omega
  have h_supply_no_overflow_raw :
      (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
    simpa using h_supply_no_overflow
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by omega
  have h_overflow :
      Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div
            (add (mul shares (add (s.storage 4) 1))
              (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    simpa using h_assets_overflow
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, setMapping,
    setStorage, safeTransferFrom, Contract.run, ContractResult.snd, Verity.bind,
    Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
    Verity.Stdlib.Math.safeAdd, h_not_balance_overflow, h_not_supply_overflow,
    h_overflow, Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_succeeds_when_accounting_does_not_overflow
theorem mint_succeeds_when_accounting_does_not_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_succeeds_when_accounting_does_not_overflow shares receiver s
    ((mint shares receiver).run s) := by
  unfold erc4626_mint_succeeds_when_accounting_does_not_overflow
  dsimp
  intro h_balance_no_overflow h_supply_no_overflow h_assets_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    have h_raw :
        (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
    have h_raw : (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_supply_no_overflow
    omega
  have h_not_assets_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div
            (add (mul shares (add (s.storage 4) 1))
              (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    have h_raw :
        (s.storage 4).val +
            (div
              (add (mul shares (add (s.storage 4) 1))
                (sub (add (s.storage 1) 1) 1))
              (add (s.storage 1) 1)).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_assets_no_overflow
    omega
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, setMapping,
    setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
    Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_credits_receiver
theorem mint_credits_receiver (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_credits_receiver shares receiver s ((mint shares receiver).run s) := by
  unfold erc4626_mint_credits_receiver
  dsimp
  intro h_balance_no_overflow h_supply_no_overflow h_assets_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    have h_raw :
        (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
    have h_raw : (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_supply_no_overflow
    omega
  have h_not_assets_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div
            (add (mul shares (add (s.storage 4) 1))
              (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    have h_raw :
        (s.storage 4).val +
            (div
              (add (mul shares (add (s.storage 4) 1))
                (sub (add (s.storage 1) 1) 1))
              (add (s.storage 1) 1)).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_assets_no_overflow
    omega
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, setMapping,
    setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
    Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_increases_total_supply
theorem mint_increases_total_supply (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_increases_total_supply shares receiver s ((mint shares receiver).run s) := by
  unfold erc4626_mint_increases_total_supply
  dsimp
  intro h_balance_no_overflow h_supply_no_overflow h_assets_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    have h_raw :
        (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
    have h_raw : (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_supply_no_overflow
    omega
  have h_not_assets_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div
            (add (mul shares (add (s.storage 4) 1))
              (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    have h_raw :
        (s.storage 4).val +
            (div
              (add (mul shares (add (s.storage 4) 1))
                (sub (add (s.storage 1) 1) 1))
              (add (s.storage 1) 1)).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_assets_no_overflow
    omega
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, setMapping,
    setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
    Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_increases_total_assets
theorem mint_increases_total_assets (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_increases_total_assets shares receiver s ((mint shares receiver).run s) := by
  unfold erc4626_mint_increases_total_assets
  dsimp
  intro h_balance_no_overflow h_supply_no_overflow h_assets_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    have h_raw :
        (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
    have h_raw : (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_supply_no_overflow
    omega
  have h_not_assets_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div
            (add (mul shares (add (s.storage 4) 1))
              (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    have h_raw :
        (s.storage 4).val +
            (div
              (add (mul shares (add (s.storage 4) 1))
                (sub (add (s.storage 1) 1) 1))
              (add (s.storage 1) 1)).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_assets_no_overflow
    omega
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, setMapping,
    setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
    Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_keeps_asset
theorem mint_keeps_asset (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_keeps_asset shares receiver s ((mint shares receiver).run s) := by
  unfold erc4626_mint_keeps_asset
  dsimp
  intro h_balance_no_overflow h_supply_no_overflow h_assets_no_overflow
  have h_not_balance_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
    have h_raw :
        (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    omega
  have h_not_supply_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
    have h_raw : (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_supply_no_overflow
    omega
  have h_not_assets_overflow :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div
            (add (mul shares (add (s.storage 4) 1))
              (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    have h_raw :
        (s.storage 4).val +
            (div
              (add (mul shares (add (s.storage 4) 1))
                (sub (add (s.storage 1) 1) 1))
              (add (s.storage 1) 1)).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_assets_no_overflow
    omega
  simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
    getStorageAddr, getStorage, getMapping, setMapping,
    setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
    Verity.pure, Pure.pure]

private theorem withdraw_properties_after_run
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  (assets.val > maxAssets.val →
    (withdraw assets receiver ownerAddr).run s = ContractResult.revert "Withdraw more than max" s) ∧
  (assets.val ≤ maxAssets.val →
    (s.sender ≠ ownerAddr →
      shares.val > (s.storageMap2 allowances.slot ownerAddr s.sender).val →
        (withdraw assets receiver ownerAddr).run s = ContractResult.revert "Insufficient allowance" s) ∧
    ((s.sender = ownerAddr ∨
        shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
      (shares.val > (s.storageMap balances.slot ownerAddr).val →
        (withdraw assets receiver ownerAddr).run s = ContractResult.revert "Insufficient balance" s) ∧
      (shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
        (shares.val > (s.storage tokenSupply.slot).val →
          (withdraw assets receiver ownerAddr).run s = ContractResult.revert "Insufficient supply" s) ∧
        (shares.val ≤ (s.storage tokenSupply.slot).val →
          (assets.val > (s.storage managedAssets.slot).val →
            (withdraw assets receiver ownerAddr).run s = ContractResult.revert "Insufficient assets" s) ∧
          (assets.val ≤ (s.storage managedAssets.slot).val →
            (withdraw assets receiver ownerAddr).run s =
              ContractResult.success shares ((withdraw assets receiver ownerAddr).run s).snd ∧
            ((withdraw assets receiver ownerAddr).run s).snd.storageMap balances.slot ownerAddr =
              Verity.EVM.Uint256.sub (s.storageMap balances.slot ownerAddr) shares ∧
            ((withdraw assets receiver ownerAddr).run s).snd.storage tokenSupply.slot =
              Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) shares ∧
            ((withdraw assets receiver ownerAddr).run s).snd.storage managedAssets.slot =
              Verity.EVM.Uint256.sub (s.storage managedAssets.slot) assets ∧
            ((s.sender = ownerAddr ∨
                s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256) →
              ((withdraw assets receiver ownerAddr).run s).snd.storageMap2 allowances.slot ownerAddr s.sender =
                s.storageMap2 allowances.slot ownerAddr s.sender) ∧
            (s.sender ≠ ownerAddr →
              s.storageMap2 allowances.slot ownerAddr s.sender ≠ maxUint256 →
                ((withdraw assets receiver ownerAddr).run s).snd.storageMap2 allowances.slot ownerAddr s.sender =
                  Verity.EVM.Uint256.sub
                    (s.storageMap2 allowances.slot ownerAddr s.sender) shares)))))) := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro h_more_than_max
    have h_more_than_max_raw :
        assets.val >
          (div (mul (s.storageMap 2 ownerAddr) (add (s.storage 4) 1)) (add (s.storage 1) 1)).val := by
      simpa using h_more_than_max
    have h_not_max :
        ¬ assets.val ≤
          (div (mul (s.storageMap 2 ownerAddr) (add (s.storage 4) 1)) (add (s.storage 1) 1)).val := by
      omega
    simp [withdraw, assetToken, balances, tokenSupply, managedAssets, msgSender,
      getStorageAddr, getStorage, getMapping, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_not_max]
  · intro h_max
    have h_max_raw :
        assets.val ≤
          (div (mul (s.storageMap 2 ownerAddr) (add (s.storage 4) 1)) (add (s.storage 1) 1)).val := by
      simpa using h_max
    refine ⟨?_, ?_⟩
    · intro h_not_owner h_insufficient_allowance
      have h_not_owner_raw : s.sender ≠ ownerAddr := by
        simpa using h_not_owner
      have h_insufficient_allowance_raw :
          (div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
              (add (s.storage 4) 1)).val >
            (s.storageMap2 3 ownerAddr s.sender).val := by
        simpa using h_insufficient_allowance
      have h_not_allowance :
          ¬ (div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
              (add (s.storage 4) 1)).val ≤
            (s.storageMap2 3 ownerAddr s.sender).val := by
        omega
      simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
        msgSender, getStorageAddr, getStorage, getMapping, getMapping2, Contract.run,
        Verity.bind, Bind.bind, Verity.require, h_max_raw, h_not_owner_raw,
        h_not_allowance, Verity.pure, Pure.pure]
    · intro h_auth
      let shares :=
        div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
          (add (s.storage 4) 1)
      have h_auth_allowance :
          s.sender ≠ ownerAddr →
            shares.val ≤ (s.storageMap2 3 ownerAddr s.sender).val := by
        intro h_ne
        rcases h_auth with h_owner | h_allow
        · exact False.elim (h_ne h_owner)
        · simpa [shares] using h_allow
      refine ⟨?_, ?_⟩
      · intro h_insufficient_balance
        have h_insufficient_balance_raw :
            shares.val > (s.storageMap 2 ownerAddr).val := by
          simpa [shares] using h_insufficient_balance
        have h_not_balance : ¬ shares.val ≤ (s.storageMap 2 ownerAddr).val := by omega
        by_cases h_owner : s.sender = ownerAddr
        · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
            maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
            setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
            h_max_raw, h_owner, h_not_balance, shares, Verity.pure, Pure.pure]
        · have h_allowance := h_auth_allowance h_owner
          simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
            maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
            setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
            h_max_raw, h_owner, h_allowance, h_not_balance, shares, Verity.pure, Pure.pure]
      · intro h_balance
        have h_balance_raw : shares.val ≤ (s.storageMap 2 ownerAddr).val := by
          simpa [shares] using h_balance
        refine ⟨?_, ?_⟩
        · intro h_insufficient_supply
          have h_insufficient_supply_raw : shares.val > (s.storage 1).val := by
            simpa [shares] using h_insufficient_supply
          have h_not_supply : ¬ shares.val ≤ (s.storage 1).val := by omega
          by_cases h_owner : s.sender = ownerAddr
          · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
              maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
              setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
              h_max_raw, h_owner, h_balance_raw, h_not_supply, shares, Verity.pure,
              Pure.pure]
          · have h_allowance := h_auth_allowance h_owner
            simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
              maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
              setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
              h_max_raw, h_owner, h_allowance, h_balance_raw, h_not_supply, shares,
              Verity.pure, Pure.pure]
        · intro h_supply
          have h_supply_raw : shares.val ≤ (s.storage 1).val := by
            simpa [shares] using h_supply
          refine ⟨?_, ?_⟩
          · intro h_insufficient_assets
            have h_insufficient_assets_raw : assets.val > (s.storage 4).val := by
              simpa using h_insufficient_assets
            have h_not_assets : ¬ assets.val ≤ (s.storage 4).val := by omega
            by_cases h_owner : s.sender = ownerAddr
            · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
                h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_not_assets, shares,
                Verity.pure, Pure.pure]
            · have h_allowance := h_auth_allowance h_owner
              simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
                h_max_raw, h_owner, h_allowance, h_balance_raw, h_supply_raw, h_not_assets,
                shares, Verity.pure, Pure.pure]
          · intro h_assets
            have h_assets_raw : assets.val ≤ (s.storage 4).val := by
              simpa using h_assets
            by_cases h_owner : s.sender = ownerAddr
            · refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                  Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                  h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_assets_raw, shares,
                  Verity.pure, Pure.pure]
              · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                  Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                  h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_assets_raw, shares,
                  Verity.pure, Pure.pure, HSub.hSub]
              · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                  Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                  h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_assets_raw, shares,
                  Verity.pure, Pure.pure, HSub.hSub]
              · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                  Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                  h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_assets_raw, shares,
                  Verity.pure, Pure.pure, HSub.hSub]
              · refine ⟨?_, ?_⟩
                · intro _h_preserve
                  simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                    h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_assets_raw, shares,
                    Verity.pure, Pure.pure]
                · intro h_not_owner _h_not_max
                  exact False.elim (h_not_owner h_owner)
            · have h_allowance := h_auth_allowance h_owner
              by_cases h_allowance_max :
                  s.storageMap2 3 ownerAddr s.sender = maxUint256
              · have h_allowance_max_raw :
                    s.storageMap2 3 ownerAddr s.sender = sub 0 1 := by
                  simpa [maxUint256] using h_allowance_max
                have h_allowance_max_bound :
                    shares.val ≤ (sub 0 1 : Uint256).val := by
                  simpa [h_allowance_max_raw] using h_allowance
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_max_raw, h_allowance_max_bound, h_balance_raw,
                    h_supply_raw, h_assets_raw, shares, Verity.pure, Pure.pure]
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_max_raw, h_allowance_max_bound, h_balance_raw,
                    h_supply_raw, h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_max_raw, h_allowance_max_bound, h_balance_raw,
                    h_supply_raw, h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_max_raw, h_allowance_max_bound, h_balance_raw,
                    h_supply_raw, h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]
                · refine ⟨?_, ?_⟩
                  · intro _h_preserve
                    simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                      maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                      setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                      emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                      Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                      h_allowance_max, h_allowance_max_raw, h_allowance_max_bound, h_balance_raw,
                      h_supply_raw, h_assets_raw, shares, Verity.pure, Pure.pure]
                  · intro _h_not_owner h_not_max
                    have h_allowance_max_spec :
                        s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256 := by
                      simpa using h_allowance_max
                    exact False.elim (h_not_max h_allowance_max_spec)
              · have h_allowance_not_max_raw :
                    s.storageMap2 3 ownerAddr s.sender ≠ sub 0 1 := by
                  simpa [maxUint256] using h_allowance_max
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_not_max_raw, h_balance_raw, h_supply_raw,
                    h_assets_raw, shares, Verity.pure, Pure.pure]
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_not_max_raw, h_balance_raw, h_supply_raw,
                    h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_not_max_raw, h_balance_raw, h_supply_raw,
                    h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]
                · simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_not_max_raw, h_balance_raw, h_supply_raw,
                    h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]
                · refine ⟨?_, ?_⟩
                  · intro h_preserve
                    rcases h_preserve with h_sender | h_max_allowance
                    · exact False.elim (h_owner h_sender)
                    · exact False.elim (h_allowance_max (by simpa using h_max_allowance))
                  · intro h_not_owner h_not_max
                    simp [withdraw, assetToken, balances, tokenSupply, managedAssets, allowances,
                      maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                      setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                      emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                      Bind.bind, Verity.require, h_max_raw, h_owner, h_allowance,
                      h_allowance_max, h_allowance_not_max_raw, h_balance_raw, h_supply_raw,
      h_assets_raw, shares, Verity.pure, Pure.pure, HSub.hSub]

-- tama: discharges=erc4626_withdraw_reverts_when_assets_exceed_max
theorem withdraw_reverts_when_assets_exceed_max
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_withdraw_reverts_when_assets_exceed_max assets receiver ownerAddr s
    ((withdraw assets receiver ownerAddr).run s) :=
  (withdraw_properties_after_run assets receiver ownerAddr s).1

-- tama: discharges=erc4626_withdraw_reverts_when_allowance_is_low
theorem withdraw_reverts_when_allowance_is_low
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_withdraw_reverts_when_allowance_is_low assets receiver ownerAddr s
    ((withdraw assets receiver ownerAddr).run s) :=
  fun h_max h_not_owner h_allowance =>
    ((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).1 h_not_owner h_allowance

-- tama: discharges=erc4626_withdraw_reverts_when_total_supply_is_low
theorem withdraw_reverts_when_total_supply_is_low
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_withdraw_reverts_when_total_supply_is_low assets receiver ownerAddr s
    ((withdraw assets receiver ownerAddr).run s) :=
  fun h_max h_auth h_balance h_supply =>
    ((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).1 h_supply

-- tama: discharges=erc4626_withdraw_reverts_when_total_assets_is_low
theorem withdraw_reverts_when_total_assets_is_low
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_withdraw_reverts_when_total_assets_is_low assets receiver ownerAddr s
    ((withdraw assets receiver ownerAddr).run s) :=
  fun h_max h_auth h_balance h_supply h_assets =>
    (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).1 h_assets

-- tama: discharges=erc4626_withdraw_succeeds_when_accounting_and_allowance_are_enough
theorem withdraw_succeeds_when_accounting_and_allowance_are_enough
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_withdraw_succeeds_when_accounting_and_allowance_are_enough assets receiver ownerAddr s
      ((withdraw assets receiver ownerAddr).run s) :=
    fun h_max h_auth h_balance h_supply h_assets =>
      let h_success := (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).2 h_assets
      h_success.1

-- tama: discharges=erc4626_withdraw_debits_owner
theorem withdraw_debits_owner
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_withdraw_debits_owner assets receiver ownerAddr s
      ((withdraw assets receiver ownerAddr).run s) :=
    fun h_max h_auth h_balance h_supply h_assets =>
      let h_success := (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).2 h_assets
      h_success.2.1

-- tama: discharges=erc4626_withdraw_decreases_total_supply
theorem withdraw_decreases_total_supply
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_withdraw_decreases_total_supply assets receiver ownerAddr s
      ((withdraw assets receiver ownerAddr).run s) :=
    fun h_max h_auth h_balance h_supply h_assets =>
      let h_success := (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).2 h_assets
      h_success.2.2.1

-- tama: discharges=erc4626_withdraw_decreases_total_assets
theorem withdraw_decreases_total_assets
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_withdraw_decreases_total_assets assets receiver ownerAddr s
      ((withdraw assets receiver ownerAddr).run s) :=
    fun h_max h_auth h_balance h_supply h_assets =>
      let h_success := (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).2 h_assets
      h_success.2.2.2.1

-- tama: discharges=erc4626_withdraw_keeps_owner_or_infinite_allowance
theorem withdraw_keeps_owner_or_infinite_allowance
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_withdraw_keeps_owner_or_infinite_allowance assets receiver ownerAddr s
      ((withdraw assets receiver ownerAddr).run s) :=
    fun h_max h_auth h_balance h_supply h_assets h_keep =>
      let h_success := (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).2 h_assets
      h_success.2.2.2.2.1 h_keep

-- tama: discharges=erc4626_withdraw_spends_finite_allowance
theorem withdraw_spends_finite_allowance
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_withdraw_spends_finite_allowance assets receiver ownerAddr s
      ((withdraw assets receiver ownerAddr).run s) :=
    fun h_max h_auth h_balance h_supply h_assets h_not_owner h_not_max =>
      let h_success := (((((withdraw_properties_after_run assets receiver ownerAddr s).2 h_max).2 h_auth).2 h_balance).2 h_supply).2 h_assets
      h_success.2.2.2.2.2 h_not_owner h_not_max

private theorem redeem_properties_after_run
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  (shares.val > (s.storageMap balances.slot ownerAddr).val →
    (redeem shares receiver ownerAddr).run s = ContractResult.revert "Redeem more than max" s) ∧
  (shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender ≠ ownerAddr →
      shares.val > (s.storageMap2 allowances.slot ownerAddr s.sender).val →
        (redeem shares receiver ownerAddr).run s = ContractResult.revert "Insufficient allowance" s) ∧
    ((s.sender = ownerAddr ∨
        shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
      (shares.val > (s.storage tokenSupply.slot).val →
        (redeem shares receiver ownerAddr).run s = ContractResult.revert "Insufficient supply" s) ∧
      (shares.val ≤ (s.storage tokenSupply.slot).val →
        (assets.val > (s.storage managedAssets.slot).val →
          (redeem shares receiver ownerAddr).run s = ContractResult.revert "Insufficient assets" s) ∧
        (assets.val ≤ (s.storage managedAssets.slot).val →
          (redeem shares receiver ownerAddr).run s =
            ContractResult.success assets ((redeem shares receiver ownerAddr).run s).snd ∧
          ((redeem shares receiver ownerAddr).run s).snd.storageMap balances.slot ownerAddr =
            Verity.EVM.Uint256.sub (s.storageMap balances.slot ownerAddr) shares ∧
          ((redeem shares receiver ownerAddr).run s).snd.storage tokenSupply.slot =
            Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) shares ∧
          ((redeem shares receiver ownerAddr).run s).snd.storage managedAssets.slot =
            Verity.EVM.Uint256.sub (s.storage managedAssets.slot) assets ∧
          ((s.sender = ownerAddr ∨
              s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256) →
            ((redeem shares receiver ownerAddr).run s).snd.storageMap2 allowances.slot ownerAddr s.sender =
              s.storageMap2 allowances.slot ownerAddr s.sender) ∧
          (s.sender ≠ ownerAddr →
            s.storageMap2 allowances.slot ownerAddr s.sender ≠ maxUint256 →
              ((redeem shares receiver ownerAddr).run s).snd.storageMap2 allowances.slot ownerAddr s.sender =
                Verity.EVM.Uint256.sub
                  (s.storageMap2 allowances.slot ownerAddr s.sender) shares))))) := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro h_more_than_max
    have h_more_than_max_raw : shares.val > (s.storageMap 2 ownerAddr).val := by
      simpa using h_more_than_max
    have h_not_balance : ¬ shares.val ≤ (s.storageMap 2 ownerAddr).val := by omega
    simp [redeem, assetToken, balances, tokenSupply, managedAssets, msgSender,
      getStorageAddr, getStorage, getMapping, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_not_balance]
  · intro h_balance
    have h_balance_raw : shares.val ≤ (s.storageMap 2 ownerAddr).val := by
      simpa using h_balance
    let assets := div (mul shares (add (s.storage 4) 1)) (add (s.storage 1) 1)
    refine ⟨?_, ?_⟩
    · intro h_not_owner h_insufficient_allowance
      have h_not_owner_raw : s.sender ≠ ownerAddr := by
        simpa using h_not_owner
      have h_insufficient_allowance_raw :
          shares.val > (s.storageMap2 3 ownerAddr s.sender).val := by
        simpa using h_insufficient_allowance
      have h_not_allowance :
          ¬ shares.val ≤ (s.storageMap2 3 ownerAddr s.sender).val := by
        omega
      simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
        msgSender, getStorageAddr, getStorage, getMapping, getMapping2, Contract.run,
        Verity.bind, Bind.bind, Verity.require, h_balance_raw, h_not_owner_raw,
        h_not_allowance, Verity.pure, Pure.pure]
    · intro h_auth
      have h_auth_allowance :
          s.sender ≠ ownerAddr →
            shares.val ≤ (s.storageMap2 3 ownerAddr s.sender).val := by
        intro h_ne
        rcases h_auth with h_owner | h_allow
        · exact False.elim (h_ne h_owner)
        · simpa using h_allow
      refine ⟨?_, ?_⟩
      · intro h_insufficient_supply
        have h_insufficient_supply_raw : shares.val > (s.storage 1).val := by
          simpa using h_insufficient_supply
        have h_not_supply : ¬ shares.val ≤ (s.storage 1).val := by omega
        by_cases h_owner : s.sender = ownerAddr
        · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
            maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
            setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
            h_balance_raw, h_owner, h_not_supply, assets, Verity.pure, Pure.pure]
        · have h_allowance := h_auth_allowance h_owner
          simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
            maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
            setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
            h_balance_raw, h_owner, h_allowance, h_not_supply, assets, Verity.pure,
            Pure.pure]
      · intro h_supply
        have h_supply_raw : shares.val ≤ (s.storage 1).val := by
          simpa using h_supply
        refine ⟨?_, ?_⟩
        · intro h_insufficient_assets
          have h_insufficient_assets_raw : assets.val > (s.storage 4).val := by
            simpa [assets] using h_insufficient_assets
          have h_not_assets : ¬ assets.val ≤ (s.storage 4).val := by omega
          by_cases h_owner : s.sender = ownerAddr
          · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
              maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
              setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
              h_balance_raw, h_owner, h_supply_raw, h_not_assets, assets, Verity.pure,
              Pure.pure]
          · have h_allowance := h_auth_allowance h_owner
            simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
              maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
              setMapping2, Contract.run, Verity.bind, Bind.bind, Verity.require,
              h_balance_raw, h_owner, h_allowance, h_supply_raw, h_not_assets, assets,
              Verity.pure, Pure.pure]
        · intro h_assets
          have h_assets_raw : assets.val ≤ (s.storage 4).val := by
            simpa [assets] using h_assets
          by_cases h_owner : s.sender = ownerAddr
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                h_balance_raw, h_owner, h_supply_raw, h_assets_raw, assets, Verity.pure,
                Pure.pure]
            · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                h_balance_raw, h_owner, h_supply_raw, h_assets_raw, assets, Verity.pure,
                Pure.pure, HSub.hSub]
            · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                h_balance_raw, h_owner, h_supply_raw, h_assets_raw, assets, Verity.pure,
                Pure.pure, HSub.hSub]
            · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                h_balance_raw, h_owner, h_supply_raw, h_assets_raw, assets, Verity.pure,
                Pure.pure, HSub.hSub]
            · refine ⟨?_, ?_⟩
              · intro _h_preserve
                simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setStorage, safeTransfer, mstore, rawLog, emitEvent,
                  Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
                  h_balance_raw, h_owner, h_supply_raw, h_assets_raw, assets, Verity.pure,
                  Pure.pure]
              · intro h_not_owner _h_not_max
                exact False.elim (h_not_owner h_owner)
          · have h_allowance := h_auth_allowance h_owner
            by_cases h_allowance_max :
                s.storageMap2 3 ownerAddr s.sender = maxUint256
            · have h_allowance_max_raw :
                  s.storageMap2 3 ownerAddr s.sender = sub 0 1 := by
                simpa [maxUint256] using h_allowance_max
              have h_allowance_max_bound :
                  shares.val ≤ (sub 0 1 : Uint256).val := by
                simpa [h_allowance_max_raw] using h_allowance
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_max_raw, h_allowance_max_bound,
                  h_supply_raw, h_assets_raw, assets, Verity.pure, Pure.pure]
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_max_raw, h_allowance_max_bound,
                  h_supply_raw, h_assets_raw, assets, Verity.pure, Pure.pure, HSub.hSub]
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_max_raw, h_allowance_max_bound,
                  h_supply_raw, h_assets_raw, assets, Verity.pure, Pure.pure, HSub.hSub]
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_max_raw, h_allowance_max_bound,
                  h_supply_raw, h_assets_raw, assets, Verity.pure, Pure.pure, HSub.hSub]
              · refine ⟨?_, ?_⟩
                · intro _h_preserve
                  simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_max_raw, h_allowance_max_bound,
                    h_supply_raw, h_assets_raw, assets, Verity.pure, Pure.pure]
                · intro _h_not_owner h_not_max
                  have h_allowance_max_spec :
                      s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256 := by
                    simpa using h_allowance_max
                  exact False.elim (h_not_max h_allowance_max_spec)
            · have h_allowance_not_max_raw :
                  s.storageMap2 3 ownerAddr s.sender ≠ sub 0 1 := by
                simpa [maxUint256] using h_allowance_max
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_not_max_raw, h_supply_raw, h_assets_raw,
                  assets, Verity.pure, Pure.pure]
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_not_max_raw, h_supply_raw, h_assets_raw,
                  assets, Verity.pure, Pure.pure, HSub.hSub]
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_not_max_raw, h_supply_raw, h_assets_raw,
                  assets, Verity.pure, Pure.pure, HSub.hSub]
              · simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                  maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                  setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                  emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                  Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                  h_allowance_max, h_allowance_not_max_raw, h_supply_raw, h_assets_raw,
                  assets, Verity.pure, Pure.pure, HSub.hSub]
              · refine ⟨?_, ?_⟩
                · intro h_preserve
                  rcases h_preserve with h_sender | h_max_allowance
                  · exact False.elim (h_owner h_sender)
                  · exact False.elim (h_allowance_max (by simpa using h_max_allowance))
                · intro h_not_owner h_not_max
                  simp [redeem, assetToken, balances, tokenSupply, managedAssets, allowances,
                    maxUint256, msgSender, getStorageAddr, getStorage, getMapping, getMapping2,
                    setMapping, setMapping2, setStorage, safeTransfer, mstore, rawLog,
                    emitEvent, Contract.run, ContractResult.snd, Verity.bind,
                    Bind.bind, Verity.require, h_balance_raw, h_owner, h_allowance,
                    h_allowance_max, h_allowance_not_max_raw, h_supply_raw, h_assets_raw,
                    assets, Verity.pure, Pure.pure, HSub.hSub]

-- tama: discharges=erc4626_redeem_reverts_when_shares_exceed_max
theorem redeem_reverts_when_shares_exceed_max
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_redeem_reverts_when_shares_exceed_max shares receiver ownerAddr s
    ((redeem shares receiver ownerAddr).run s) :=
  (redeem_properties_after_run shares receiver ownerAddr s).1

-- tama: discharges=erc4626_redeem_reverts_when_allowance_is_low
theorem redeem_reverts_when_allowance_is_low
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_redeem_reverts_when_allowance_is_low shares receiver ownerAddr s
    ((redeem shares receiver ownerAddr).run s) :=
  fun h_balance h_not_owner h_allowance =>
    ((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).1 h_not_owner h_allowance

-- tama: discharges=erc4626_redeem_reverts_when_total_supply_is_low
theorem redeem_reverts_when_total_supply_is_low
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_redeem_reverts_when_total_supply_is_low shares receiver ownerAddr s
    ((redeem shares receiver ownerAddr).run s) :=
  fun h_balance h_auth h_supply =>
    (((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).1 h_supply

-- tama: discharges=erc4626_redeem_succeeds_when_accounting_and_allowance_are_enough
theorem redeem_succeeds_when_accounting_and_allowance_are_enough
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_redeem_succeeds_when_accounting_and_allowance_are_enough shares receiver ownerAddr s
      ((redeem shares receiver ownerAddr).run s) :=
    fun h_balance h_auth h_supply h_assets =>
      let h_success := ((((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).2 h_supply).2 h_assets
      h_success.1

-- tama: discharges=erc4626_redeem_debits_owner
theorem redeem_debits_owner
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_redeem_debits_owner shares receiver ownerAddr s
      ((redeem shares receiver ownerAddr).run s) :=
    fun h_balance h_auth h_supply h_assets =>
      let h_success := ((((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).2 h_supply).2 h_assets
      h_success.2.1

-- tama: discharges=erc4626_redeem_decreases_total_supply
theorem redeem_decreases_total_supply
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_redeem_decreases_total_supply shares receiver ownerAddr s
      ((redeem shares receiver ownerAddr).run s) :=
    fun h_balance h_auth h_supply h_assets =>
      let h_success := ((((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).2 h_supply).2 h_assets
      h_success.2.2.1

-- tama: discharges=erc4626_redeem_decreases_total_assets
theorem redeem_decreases_total_assets
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_redeem_decreases_total_assets shares receiver ownerAddr s
      ((redeem shares receiver ownerAddr).run s) :=
    fun h_balance h_auth h_supply h_assets =>
      let h_success := ((((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).2 h_supply).2 h_assets
      h_success.2.2.2.1

-- tama: discharges=erc4626_redeem_keeps_owner_or_infinite_allowance
theorem redeem_keeps_owner_or_infinite_allowance
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_redeem_keeps_owner_or_infinite_allowance shares receiver ownerAddr s
      ((redeem shares receiver ownerAddr).run s) :=
    fun h_balance h_auth h_supply h_assets h_keep =>
      let h_success := ((((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).2 h_supply).2 h_assets
      h_success.2.2.2.2.1 h_keep

-- tama: discharges=erc4626_redeem_spends_finite_allowance
theorem redeem_spends_finite_allowance
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
    erc4626_redeem_spends_finite_allowance shares receiver ownerAddr s
      ((redeem shares receiver ownerAddr).run s) :=
    fun h_balance h_auth h_supply h_assets h_not_owner h_not_max =>
      let h_success := ((((redeem_properties_after_run shares receiver ownerAddr s).2 h_balance).2 h_auth).2 h_supply).2 h_assets
      h_success.2.2.2.2.2 h_not_owner h_not_max

-- tama: discharges=erc4626_deposit_returns_at_least_preview
theorem deposit_returns_at_least_preview
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_returns_at_least_preview assets receiver s
    ((deposit assets receiver).run s) := by
  intro h_balance h_supply h_assets
  refine ⟨deposit_succeeds_when_accounting_does_not_overflow assets receiver s
    h_balance h_supply h_assets, ?_⟩
  simp [previewDeposit, convertToShares, depositShares, tokenSupply, managedAssets,
    getStorageAddr, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure,
    Bind.bind, Pure.pure]

-- tama: discharges=erc4626_mint_pulls_no_more_than_preview
theorem mint_pulls_no_more_than_preview
    (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_pulls_no_more_than_preview shares receiver s
    ((mint shares receiver).run s) := by
  intro h_balance h_supply h_assets
  refine ⟨mint_succeeds_when_accounting_does_not_overflow shares receiver s
    h_balance h_supply h_assets, ?_⟩
  simp [previewMint, mintAssets, tokenSupply, managedAssets, getStorageAddr, getStorage,
    Contract.run, ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_withdraw_burns_no_more_than_preview
theorem withdraw_burns_no_more_than_preview
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_withdraw_burns_no_more_than_preview assets receiver ownerAddr s
    ((withdraw assets receiver ownerAddr).run s) := by
  intro h_max h_auth h_balance h_supply h_assets
  refine ⟨withdraw_succeeds_when_accounting_and_allowance_are_enough assets receiver ownerAddr s
    h_max h_auth h_balance h_supply h_assets, ?_⟩
  simp [previewWithdraw, withdrawShares, tokenSupply, managedAssets, getStorageAddr, getStorage,
    Contract.run, ContractResult.fst, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_redeem_returns_at_least_preview
theorem redeem_returns_at_least_preview
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_redeem_returns_at_least_preview shares receiver ownerAddr s
    ((redeem shares receiver ownerAddr).run s) := by
  intro h_balance h_auth h_supply h_assets
  refine ⟨redeem_succeeds_when_accounting_and_allowance_are_enough shares receiver ownerAddr s
    h_balance h_auth h_supply h_assets, ?_⟩
  simp [previewRedeem, convertToAssets, redeemAssets, tokenSupply, managedAssets,
    getStorageAddr, getStorage, Contract.run, ContractResult.fst, Verity.bind, Verity.pure,
    Bind.bind, Pure.pure]

-- tama: discharges=erc4626_deposit_pulls_assets_from_sender
theorem deposit_pulls_assets_from_sender
    (assets : Uint256) (receiver : Address) (pre : AssetBalances) (s : ContractState) :
  erc4626_deposit_pulls_assets_from_sender assets receiver pre s
    ((deposit assets receiver).run s) := by
  intro h_balance h_supply h_assets
  have h_not_balance :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap balances.slot receiver).val + (depositShares assets s).val := by
    omega
  have h_not_supply :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage tokenSupply.slot).val + (depositShares assets s).val := by
    omega
  have h_not_assets :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage managedAssets.slot).val + assets.val := by
    omega
  have h_not_balance_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap 2 receiver).val +
          (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
    simpa [depositShares, balances, tokenSupply, managedAssets] using h_not_balance
  have h_not_supply_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 1).val +
          (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
    simpa [depositShares, tokenSupply, managedAssets] using h_not_supply
  have h_not_assets_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 4).val + assets.val := by
    simpa [managedAssets] using h_not_assets
  refine ⟨?_, ?_⟩
  · simp [hasSafeTransferFromTrace, assetTraceContains, deposit, depositShares,
      getStorageAddr, getStorage, getMapping, setMapping, setStorage, msgSender,
      Verity.contractAddress, safeTransferFrom, mstore, rawLog, emitEvent,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_not_balance_raw, h_not_supply_raw, h_not_assets_raw, Verity.pure, Pure.pure]
  · by_cases h_same : s.sender = s.thisAddress
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬s.thisAddress = s.sender := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_deposit_increases_vault_asset_balance
theorem deposit_increases_vault_asset_balance
    (assets : Uint256) (receiver : Address) (pre : AssetBalances) (s : ContractState) :
  erc4626_deposit_increases_vault_asset_balance assets receiver pre s
    ((deposit assets receiver).run s) := by
  intro h_balance h_supply h_assets
  have h_not_balance :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap balances.slot receiver).val + (depositShares assets s).val := by
    omega
  have h_not_supply :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage tokenSupply.slot).val + (depositShares assets s).val := by
    omega
  have h_not_assets :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage managedAssets.slot).val + assets.val := by
    omega
  have h_not_balance_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap 2 receiver).val +
          (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
    simpa [depositShares, balances, tokenSupply, managedAssets] using h_not_balance
  have h_not_supply_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 1).val +
          (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
    simpa [depositShares, tokenSupply, managedAssets] using h_not_supply
  have h_not_assets_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 4).val + assets.val := by
    simpa [managedAssets] using h_not_assets
  refine ⟨?_, ?_⟩
  · simp [hasSafeTransferFromTrace, assetTraceContains, deposit, depositShares,
      getStorageAddr, getStorage, getMapping, setMapping, setStorage, msgSender,
      Verity.contractAddress, safeTransferFrom, mstore, rawLog, emitEvent,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_not_balance_raw, h_not_supply_raw, h_not_assets_raw, Verity.pure, Pure.pure]
  · by_cases h_same : s.sender = s.thisAddress
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬s.thisAddress = s.sender := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_mint_pulls_required_assets_from_sender
theorem mint_pulls_required_assets_from_sender
    (shares : Uint256) (receiver : Address) (pre : AssetBalances) (s : ContractState) :
  erc4626_mint_pulls_required_assets_from_sender shares receiver pre s
    ((mint shares receiver).run s) := by
  intro h_balance h_supply h_assets
  have h_not_balance :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap balances.slot receiver).val + shares.val := by
    omega
  have h_not_supply :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage tokenSupply.slot).val + shares.val := by
    omega
  have h_not_assets :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage managedAssets.slot).val + (mintAssets shares s).val := by
    omega
  have h_not_balance_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap 2 receiver).val + shares.val := by
    simpa [balances] using h_not_balance
  have h_not_supply_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 1).val + shares.val := by
    simpa [tokenSupply] using h_not_supply
  have h_not_assets_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div (add (mul shares (add (s.storage 4) 1)) (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    simpa [mintAssets, tokenSupply, managedAssets] using h_not_assets
  refine ⟨?_, ?_⟩
  · simp [hasSafeTransferFromTrace, assetTraceContains, mint, mintAssets,
      getStorageAddr, getStorage, getMapping, setMapping, setStorage, msgSender,
      Verity.contractAddress, safeTransferFrom, mstore, rawLog, emitEvent,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_not_balance_raw, h_not_supply_raw, h_not_assets_raw, Verity.pure, Pure.pure]
  · by_cases h_same : s.sender = s.thisAddress
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬s.thisAddress = s.sender := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_mint_increases_vault_asset_balance
theorem mint_increases_vault_asset_balance
    (shares : Uint256) (receiver : Address) (pre : AssetBalances) (s : ContractState) :
  erc4626_mint_increases_vault_asset_balance shares receiver pre s
    ((mint shares receiver).run s) := by
  intro h_balance h_supply h_assets
  have h_not_balance :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap balances.slot receiver).val + shares.val := by
    omega
  have h_not_supply :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage tokenSupply.slot).val + shares.val := by
    omega
  have h_not_assets :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage managedAssets.slot).val + (mintAssets shares s).val := by
    omega
  have h_not_balance_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap 2 receiver).val + shares.val := by
    simpa [balances] using h_not_balance
  have h_not_supply_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 1).val + shares.val := by
    simpa [tokenSupply] using h_not_supply
  have h_not_assets_raw :
      ¬ Verity.Stdlib.Math.MAX_UINT256 <
        (s.storage 4).val +
          (div (add (mul shares (add (s.storage 4) 1)) (sub (add (s.storage 1) 1) 1))
            (add (s.storage 1) 1)).val := by
    simpa [mintAssets, tokenSupply, managedAssets] using h_not_assets
  refine ⟨?_, ?_⟩
  · simp [hasSafeTransferFromTrace, assetTraceContains, mint, mintAssets,
      getStorageAddr, getStorage, getMapping, setMapping, setStorage, msgSender,
      Verity.contractAddress, safeTransferFrom, mstore, rawLog, emitEvent,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
      h_not_balance_raw, h_not_supply_raw, h_not_assets_raw, Verity.pure, Pure.pure]
  · by_cases h_same : s.sender = s.thisAddress
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬s.thisAddress = s.sender := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_withdraw_sends_assets_to_receiver
theorem withdraw_sends_assets_to_receiver
    (assets : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) :
  erc4626_withdraw_sends_assets_to_receiver assets receiver ownerAddr pre s
    ((withdraw assets receiver ownerAddr).run s) := by
  intro h_max h_auth h_balance h_supply h_assets
  have h_max_raw :
      assets.val ≤
        (div (mul (s.storageMap 2 ownerAddr) (add (s.storage 4) 1))
          (add (s.storage 1) 1)).val := by
    simpa [balances, tokenSupply, managedAssets] using h_max
  have h_balance_raw :
      (div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
        (add (s.storage 4) 1)).val ≤ (s.storageMap 2 ownerAddr).val := by
    simpa [withdrawShares, balances, tokenSupply, managedAssets] using h_balance
  have h_supply_raw :
      (div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
        (add (s.storage 4) 1)).val ≤ (s.storage 1).val := by
    simpa [withdrawShares, tokenSupply, managedAssets] using h_supply
  have h_assets_raw : assets.val ≤ (s.storage 4).val := by
    simpa [managedAssets] using h_assets
  refine ⟨?_, ?_⟩
  · by_cases h_owner : s.sender = ownerAddr
    · simp [hasSafeTransferTrace, assetTraceContains, withdraw, withdrawShares,
        getStorageAddr, getStorage, getMapping, getMapping2, setMapping, setMapping2,
        setStorage, msgSender, safeTransfer, mstore, rawLog, emitEvent,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        h_max_raw, h_owner, h_balance_raw, h_supply_raw, h_assets_raw,
        Verity.pure, Pure.pure]
    · have h_allowance : (withdrawShares assets s).val ≤
          (s.storageMap2 allowances.slot ownerAddr s.sender).val := by
        exact h_auth.resolve_left h_owner
      have h_allowance_raw :
          (div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
            (add (s.storage 4) 1)).val ≤ (s.storageMap2 3 ownerAddr s.sender).val := by
        simpa [withdrawShares, allowances, tokenSupply, managedAssets] using h_allowance
      by_cases h_allowance_max : s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256
      · have h_allowance_max_raw :
            s.storageMap2 3 ownerAddr s.sender = sub 0 1 := by
          simpa [allowances, maxUint256] using h_allowance_max
        have h_allowance_max_bound :
            (div (add (mul assets (add (s.storage 1) 1)) (sub (add (s.storage 4) 1) 1))
              (add (s.storage 4) 1)).val ≤ (sub 0 1 : Uint256).val := by
          simpa [h_allowance_max_raw] using h_allowance_raw
        simp [hasSafeTransferTrace, assetTraceContains, withdraw, withdrawShares,
          getStorageAddr, getStorage, getMapping, getMapping2, setMapping, setMapping2,
          setStorage, msgSender, safeTransfer, mstore, rawLog, emitEvent,
          Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          h_max_raw, h_owner, h_allowance_raw, h_allowance_max_raw,
          h_allowance_max_bound, h_balance_raw, h_supply_raw, h_assets_raw,
          Verity.pure, Pure.pure]
      · have h_allowance_not_max_raw :
            s.storageMap2 3 ownerAddr s.sender ≠ sub 0 1 := by
          simpa [allowances, maxUint256] using h_allowance_max
        simp [hasSafeTransferTrace, assetTraceContains, withdraw, withdrawShares,
          getStorageAddr, getStorage, getMapping, getMapping2, setMapping, setMapping2,
          setStorage, msgSender, safeTransfer, mstore, rawLog, emitEvent,
          Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          h_max_raw, h_owner, h_allowance_raw, h_allowance_not_max_raw, h_balance_raw,
          h_supply_raw, h_assets_raw, Verity.pure, Pure.pure]
  · by_cases h_same : receiver = s.thisAddress
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬s.thisAddress = receiver := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_withdraw_decreases_vault_asset_balance
theorem withdraw_decreases_vault_asset_balance
    (assets : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) :
  erc4626_withdraw_decreases_vault_asset_balance assets receiver ownerAddr pre s
    ((withdraw assets receiver ownerAddr).run s) := by
  intro h_max h_auth h_balance h_supply h_assets
  refine ⟨?_, ?_⟩
  · exact (withdraw_sends_assets_to_receiver assets receiver ownerAddr pre s
      h_max h_auth h_balance h_supply h_assets).1
  · by_cases h_same : s.thisAddress = receiver
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬receiver = s.thisAddress := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_redeem_sends_redeemed_assets_to_receiver
theorem redeem_sends_redeemed_assets_to_receiver
    (shares : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) :
  erc4626_redeem_sends_redeemed_assets_to_receiver shares receiver ownerAddr pre s
    ((redeem shares receiver ownerAddr).run s) := by
  intro h_balance h_auth h_supply h_assets
  have h_balance_raw : shares.val ≤ (s.storageMap 2 ownerAddr).val := by
    simpa [balances] using h_balance
  have h_supply_raw : shares.val ≤ (s.storage 1).val := by
    simpa [tokenSupply] using h_supply
  have h_assets_raw :
      (div (mul shares (add (s.storage 4) 1)) (add (s.storage 1) 1)).val ≤
        (s.storage 4).val := by
    simpa [redeemAssets, tokenSupply, managedAssets] using h_assets
  refine ⟨?_, ?_⟩
  · by_cases h_owner : s.sender = ownerAddr
    · simp [hasSafeTransferTrace, assetTraceContains, redeem, redeemAssets,
        getStorageAddr, getStorage, getMapping, getMapping2, setMapping, setMapping2,
        setStorage, msgSender, safeTransfer, mstore, rawLog, emitEvent,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        h_balance_raw, h_owner, h_supply_raw, h_assets_raw, Verity.pure, Pure.pure]
    · have h_allowance : shares.val ≤
          (s.storageMap2 allowances.slot ownerAddr s.sender).val := by
        exact h_auth.resolve_left h_owner
      have h_allowance_raw : shares.val ≤ (s.storageMap2 3 ownerAddr s.sender).val := by
        simpa [allowances] using h_allowance
      by_cases h_allowance_max : s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256
      · have h_allowance_max_raw :
            s.storageMap2 3 ownerAddr s.sender = sub 0 1 := by
          simpa [allowances, maxUint256] using h_allowance_max
        have h_allowance_max_bound : shares.val ≤ (sub 0 1 : Uint256).val := by
          simpa [h_allowance_max_raw] using h_allowance_raw
        simp [hasSafeTransferTrace, assetTraceContains, redeem, redeemAssets,
          getStorageAddr, getStorage, getMapping, getMapping2, setMapping, setMapping2,
          setStorage, msgSender, safeTransfer, mstore, rawLog, emitEvent,
          Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          h_balance_raw, h_owner, h_allowance_raw, h_allowance_max_raw,
          h_allowance_max_bound, h_supply_raw, h_assets_raw, Verity.pure, Pure.pure]
      · have h_allowance_not_max_raw :
            s.storageMap2 3 ownerAddr s.sender ≠ sub 0 1 := by
          simpa [allowances, maxUint256] using h_allowance_max
        simp [hasSafeTransferTrace, assetTraceContains, redeem, redeemAssets,
          getStorageAddr, getStorage, getMapping, getMapping2, setMapping, setMapping2,
          setStorage, msgSender, safeTransfer, mstore, rawLog, emitEvent,
          Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
          h_balance_raw, h_owner, h_allowance_raw, h_allowance_not_max_raw, h_supply_raw, h_assets_raw,
          Verity.pure, Pure.pure]
  · by_cases h_same : receiver = s.thisAddress
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬s.thisAddress = receiver := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_redeem_decreases_vault_asset_balance
theorem redeem_decreases_vault_asset_balance
    (shares : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) :
  erc4626_redeem_decreases_vault_asset_balance shares receiver ownerAddr pre s
    ((redeem shares receiver ownerAddr).run s) := by
  intro h_balance h_auth h_supply h_assets
  refine ⟨?_, ?_⟩
  · exact (redeem_sends_redeemed_assets_to_receiver shares receiver ownerAddr pre s
      h_balance h_auth h_supply h_assets).1
  · by_cases h_same : s.thisAddress = receiver
    · simp [assetWorldAfterTransfer, h_same]
    · have h_same_rev : ¬receiver = s.thisAddress := by
        intro h
        exact h_same h.symm
      simp [assetWorldAfterTransfer, h_same, h_same_rev]

-- tama: discharges=erc4626_deposit_revert_keeps_asset_balances
theorem deposit_revert_keeps_asset_balances
    (assets : Uint256) (receiver : Address) (pre post : AssetBalances) (s : ContractState)
    (h_no_external_transfer :
      revertedWithOriginalState s ((deposit assets receiver).run s) →
        assetBalancesUnchanged pre post) :
  erc4626_deposit_revert_keeps_asset_balances assets receiver pre post s
    ((deposit assets receiver).run s) :=
  h_no_external_transfer

-- tama: discharges=erc4626_mint_revert_keeps_asset_balances
theorem mint_revert_keeps_asset_balances
    (shares : Uint256) (receiver : Address) (pre post : AssetBalances) (s : ContractState)
    (h_no_external_transfer :
      revertedWithOriginalState s ((mint shares receiver).run s) →
        assetBalancesUnchanged pre post) :
  erc4626_mint_revert_keeps_asset_balances shares receiver pre post s
    ((mint shares receiver).run s) :=
  h_no_external_transfer

-- tama: discharges=erc4626_withdraw_revert_keeps_asset_balances
theorem withdraw_revert_keeps_asset_balances
    (assets : Uint256) (receiver ownerAddr : Address) (pre post : AssetBalances)
    (s : ContractState)
    (h_no_external_transfer :
      revertedWithOriginalState s ((withdraw assets receiver ownerAddr).run s) →
        assetBalancesUnchanged pre post) :
  erc4626_withdraw_revert_keeps_asset_balances assets receiver ownerAddr pre post s
    ((withdraw assets receiver ownerAddr).run s) :=
  h_no_external_transfer

-- tama: discharges=erc4626_redeem_revert_keeps_asset_balances
theorem redeem_revert_keeps_asset_balances
    (shares : Uint256) (receiver ownerAddr : Address) (pre post : AssetBalances)
    (s : ContractState)
    (h_no_external_transfer :
      revertedWithOriginalState s ((redeem shares receiver ownerAddr).run s) →
        assetBalancesUnchanged pre post) :
  erc4626_redeem_revert_keeps_asset_balances shares receiver ownerAddr pre post s
    ((redeem shares receiver ownerAddr).run s) :=
  h_no_external_transfer

-- tama: discharges=erc4626_no_donation_deposit_preserves_backing
theorem no_donation_deposit_preserves_backing
    (assets : Uint256) (receiver : Address) (pre : AssetBalances) (s : ContractState) :
  erc4626_no_donation_deposit_preserves_backing assets receiver pre s
    ((deposit assets receiver).run s) := by
  intro h_pre h_sender h_balance h_supply h_assets
  have h_asset :=
    deposit_increases_vault_asset_balance assets receiver pre s h_balance h_supply h_assets
  have h_managed :=
    deposit_increases_total_assets assets receiver s h_balance h_supply h_assets
  refine ⟨h_asset.1, ?_⟩
  rw [h_asset.2]
  rw [if_neg h_sender]
  rw [h_pre]
  exact h_managed.symm

-- tama: discharges=erc4626_no_donation_mint_preserves_backing
theorem no_donation_mint_preserves_backing
    (shares : Uint256) (receiver : Address) (pre : AssetBalances) (s : ContractState) :
  erc4626_no_donation_mint_preserves_backing shares receiver pre s
    ((mint shares receiver).run s) := by
  intro h_pre h_sender h_balance h_supply h_assets
  have h_asset :=
    mint_increases_vault_asset_balance shares receiver pre s h_balance h_supply h_assets
  have h_managed :=
    mint_increases_total_assets shares receiver s h_balance h_supply h_assets
  refine ⟨h_asset.1, ?_⟩
  rw [h_asset.2]
  rw [if_neg h_sender]
  rw [h_pre]
  exact h_managed.symm

-- tama: discharges=erc4626_no_donation_withdraw_preserves_backing
theorem no_donation_withdraw_preserves_backing
    (assets : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) :
  erc4626_no_donation_withdraw_preserves_backing assets receiver ownerAddr pre s
    ((withdraw assets receiver ownerAddr).run s) := by
  intro h_pre h_receiver h_max h_auth h_balance h_supply h_assets
  have h_asset :=
    withdraw_decreases_vault_asset_balance assets receiver ownerAddr pre s
      h_max h_auth h_balance h_supply h_assets
  have h_managed :=
    withdraw_decreases_total_assets assets receiver ownerAddr s
      h_max h_auth h_balance h_supply h_assets
  refine ⟨h_asset.1, ?_⟩
  rw [h_asset.2]
  rw [if_neg h_receiver]
  rw [h_pre]
  exact h_managed.symm

-- tama: discharges=erc4626_no_donation_redeem_preserves_backing
theorem no_donation_redeem_preserves_backing
    (shares : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) :
  erc4626_no_donation_redeem_preserves_backing shares receiver ownerAddr pre s
    ((redeem shares receiver ownerAddr).run s) := by
  intro h_pre h_receiver h_balance h_auth h_supply h_assets
  have h_asset :=
    redeem_decreases_vault_asset_balance shares receiver ownerAddr pre s
      h_balance h_auth h_supply h_assets
  have h_managed :=
    redeem_decreases_total_assets shares receiver ownerAddr s
      h_balance h_auth h_supply h_assets
  refine ⟨h_asset.1, ?_⟩
  rw [h_asset.2]
  rw [if_neg h_receiver]
  rw [h_pre]
  exact h_managed.symm

private theorem approve_keeps_managed_assets_storage
    (spender : Address) (amount : Uint256) (s : ContractState) :
  ((approve spender amount).run s).snd.storage managedAssets.slot =
    s.storage managedAssets.slot := by
  simp [approve, allowances, managedAssets, msgSender, setMapping2, Contract.run,
    ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

private theorem approve_keeps_token_supply_storage
    (spender : Address) (amount : Uint256) (s : ContractState) :
  ((approve spender amount).run s).snd.storage tokenSupply.slot =
    s.storage tokenSupply.slot := by
  simpa [erc4626_approve_keeps_total_supply,
    Tamago.Spec.Tokens.ERC20Spec.erc20_approve_keeps_total_supply,
    Tamago.Tokens.ERC20.tokenSupply, tokenSupply]
    using approve_keeps_total_supply spender amount s

private theorem transfer_keeps_managed_assets_storage
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  ((transfer toAddr amount).run s).snd.storage managedAssets.slot =
    s.storage managedAssets.slot := by
  by_cases h_balance : amount.val ≤ (s.storageMap 2 s.sender).val
  · by_cases h_same : s.sender = toAddr
    · subst h_same
      simp [transfer, balances, managedAssets, msgSender, getMapping, Contract.run,
        ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, h_balance]
    · by_cases h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 toAddr).val + amount.val
      · simp [transfer, balances, managedAssets, msgSender, getMapping, setMapping,
          Contract.run, ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
      · simp [transfer, balances, managedAssets, msgSender, getMapping, setMapping,
          Contract.run, ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
  · simp [transfer, balances, managedAssets, msgSender, getMapping, Contract.run,
      ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.require, h_balance]

private theorem transfer_keeps_token_supply_storage
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  ((transfer toAddr amount).run s).snd.storage tokenSupply.slot =
    s.storage tokenSupply.slot := by
  simpa [erc4626_transfer_keeps_total_supply,
    Tamago.Spec.Tokens.ERC20Spec.erc20_transfer_keeps_total_supply,
    Tamago.Tokens.ERC20.tokenSupply, tokenSupply]
    using transfer_keeps_total_supply toAddr amount s

private theorem transferFrom_keeps_managed_assets_storage
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  ((transferFrom fromAddr toAddr amount).run s).snd.storage managedAssets.slot =
    s.storage managedAssets.slot := by
  by_cases h_allowance :
      amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val
  · by_cases h_balance : amount.val ≤ (s.storageMap 2 fromAddr).val
    · by_cases h_same : fromAddr = toAddr
      · subst h_same
        by_cases h_max :
          s.storageMap2 3 fromAddr s.sender = (sub 0 1 : Uint256)
        · have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
            simpa [h_max] using h_allowance
          simp [transferFrom, allowances, balances, managedAssets, maxUint256,
            msgSender, getMapping2, getMapping, setMapping2, Contract.run,
            ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
            Verity.require, h_allowance, h_allowance_max, h_balance, h_max]
        · simp [transferFrom, allowances, balances, managedAssets, maxUint256,
            msgSender, getMapping2, getMapping, setMapping2, Contract.run,
            ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
            Verity.require, h_allowance, h_balance, h_max]
      · by_cases h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 2 toAddr).val + amount.val
        · simp [transferFrom, allowances, balances, managedAssets, msgSender,
            getMapping2, getMapping, setMapping, Contract.run, ContractResult.snd,
            getStorageAddr, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            h_allowance, h_balance, h_same, h_overflow]
        · by_cases h_max :
            s.storageMap2 3 fromAddr s.sender = (sub 0 1 : Uint256)
          · have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
              simpa [h_max] using h_allowance
            simp [transferFrom, allowances, balances, managedAssets, maxUint256,
              msgSender, getMapping2, getMapping, setMapping, setMapping2,
              Contract.run, ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind,
              Verity.pure, Pure.pure, Verity.require,
              Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
              h_allowance, h_allowance_max, h_balance, h_same, h_overflow, h_max]
          · simp [transferFrom, allowances, balances, managedAssets, maxUint256,
              msgSender, getMapping2, getMapping, setMapping, setMapping2,
              Contract.run, ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind,
              Verity.pure, Pure.pure, Verity.require,
              Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
              h_allowance, h_balance, h_same, h_overflow, h_max]
    · simp [transferFrom, allowances, balances, managedAssets, msgSender, getMapping2,
        getMapping, Contract.run, ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind,
        Verity.require, h_allowance, h_balance]
  · simp [transferFrom, allowances, managedAssets, msgSender, getMapping2, Contract.run,
      ContractResult.snd, getStorageAddr, Verity.bind, Bind.bind, Verity.require, h_allowance]

private theorem transferFrom_keeps_token_supply_storage
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  ((transferFrom fromAddr toAddr amount).run s).snd.storage tokenSupply.slot =
    s.storage tokenSupply.slot := by
  simpa [erc4626_transferFrom_keeps_total_supply,
    Tamago.Spec.Tokens.ERC20Spec.erc20_transferFrom_keeps_total_supply,
    Tamago.Tokens.ERC20.tokenSupply, tokenSupply]
    using transferFrom_keeps_total_supply fromAddr toAddr amount s

-- tama: discharges=erc4626_donation_permitted_backing_covers_total_assets
theorem donation_permitted_backing_covers_total_assets
    (vault : Address) (assetBalances : AssetBalances) (s : ContractState)
    (h_cover : (s.storage managedAssets.slot).val ≤ (assetBalances vault).val) :
  erc4626_donation_permitted_backing_covers_total_assets vault assetBalances s :=
  h_cover

-- tama: discharges=erc4626_transfer_keeps_total_assets_and_backing
theorem transfer_keeps_total_assets_and_backing
    (toAddr vault : Address) (amount : Uint256) (assetBalances : AssetBalances)
    (s : ContractState) :
  erc4626_transfer_keeps_total_assets_and_backing toAddr amount vault assetBalances s
    ((transfer toAddr amount).run s) := by
  have h_totalAssets := transfer_keeps_managed_assets_storage toAddr amount s
  refine ⟨h_totalAssets, ?_⟩
  intro h_backing
  rw [h_totalAssets]
  exact h_backing

-- tama: discharges=erc4626_transferFrom_keeps_total_assets_and_backing
theorem transferFrom_keeps_total_assets_and_backing
    (fromAddr toAddr vault : Address) (amount : Uint256) (assetBalances : AssetBalances)
    (s : ContractState) :
  erc4626_transferFrom_keeps_total_assets_and_backing fromAddr toAddr amount vault assetBalances s
    ((transferFrom fromAddr toAddr amount).run s) := by
  have h_totalAssets := transferFrom_keeps_managed_assets_storage fromAddr toAddr amount s
  refine ⟨h_totalAssets, ?_⟩
  intro h_backing
  rw [h_totalAssets]
  exact h_backing

-- tama: discharges=erc4626_approve_keeps_total_assets_and_backing
theorem approve_keeps_total_assets_and_backing
    (spender vault : Address) (amount : Uint256) (assetBalances : AssetBalances)
    (s : ContractState) :
  erc4626_approve_keeps_total_assets_and_backing spender amount vault assetBalances s
    ((approve spender amount).run s) := by
  have h_totalAssets := approve_keeps_managed_assets_storage spender amount s
  refine ⟨h_totalAssets, ?_⟩
  intro h_backing
  rw [h_totalAssets]
  exact h_backing

-- tama: discharges=erc4626_deposit_preserves_fixed_share_value
theorem deposit_preserves_fixed_share_value
    (fixedShares assets : Uint256) (receiver : Address) (s : ContractState)
    (h_no_loss :
      erc4626_deposit_succeeds_when_accounting_does_not_overflow assets receiver s
          ((deposit assets receiver).run s) →
        (fixedShareAssets fixedShares s).val ≤
          (fixedShareAssets fixedShares ((deposit assets receiver).run s).snd).val) :
  erc4626_deposit_preserves_fixed_share_value fixedShares assets receiver s
    ((deposit assets receiver).run s) :=
  h_no_loss

-- tama: discharges=erc4626_mint_preserves_fixed_share_value
theorem mint_preserves_fixed_share_value
    (fixedShares shares : Uint256) (receiver : Address) (s : ContractState)
    (h_no_loss :
      erc4626_mint_succeeds_when_accounting_does_not_overflow shares receiver s
          ((mint shares receiver).run s) →
        (fixedShareAssets fixedShares s).val ≤
          (fixedShareAssets fixedShares ((mint shares receiver).run s).snd).val) :
  erc4626_mint_preserves_fixed_share_value fixedShares shares receiver s
    ((mint shares receiver).run s) :=
  h_no_loss

-- tama: discharges=erc4626_withdraw_preserves_fixed_share_value
theorem withdraw_preserves_fixed_share_value
    (fixedShares assets : Uint256) (receiver ownerAddr : Address) (s : ContractState)
    (h_no_loss :
      erc4626_withdraw_succeeds_when_accounting_and_allowance_are_enough assets receiver ownerAddr s
          ((withdraw assets receiver ownerAddr).run s) →
        (fixedShareAssets fixedShares s).val ≤
          (fixedShareAssets fixedShares ((withdraw assets receiver ownerAddr).run s).snd).val) :
  erc4626_withdraw_preserves_fixed_share_value fixedShares assets receiver ownerAddr s
    ((withdraw assets receiver ownerAddr).run s) :=
  h_no_loss

-- tama: discharges=erc4626_redeem_preserves_fixed_share_value
theorem redeem_preserves_fixed_share_value
    (fixedShares shares : Uint256) (receiver ownerAddr : Address) (s : ContractState)
    (h_no_loss :
      erc4626_redeem_succeeds_when_accounting_and_allowance_are_enough shares receiver ownerAddr s
          ((redeem shares receiver ownerAddr).run s) →
        (fixedShareAssets fixedShares s).val ≤
          (fixedShareAssets fixedShares ((redeem shares receiver ownerAddr).run s).snd).val) :
  erc4626_redeem_preserves_fixed_share_value fixedShares shares receiver ownerAddr s
    ((redeem shares receiver ownerAddr).run s) :=
  h_no_loss

-- tama: discharges=erc4626_transfer_keeps_convertToAssets
theorem transfer_keeps_convertToAssets
    (fixedShares : Uint256) (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_keeps_convertToAssets fixedShares toAddr amount s
    ((transfer toAddr amount).run s) := by
  unfold erc4626_transfer_keeps_convertToAssets fixedShareAssets
  rw [transfer_keeps_managed_assets_storage toAddr amount s]
  rw [transfer_keeps_token_supply_storage toAddr amount s]

-- tama: discharges=erc4626_transferFrom_keeps_convertToAssets
theorem transferFrom_keeps_convertToAssets
    (fixedShares : Uint256) (fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) :
  erc4626_transferFrom_keeps_convertToAssets fixedShares fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) := by
  unfold erc4626_transferFrom_keeps_convertToAssets fixedShareAssets
  rw [transferFrom_keeps_managed_assets_storage fromAddr toAddr amount s]
  rw [transferFrom_keeps_token_supply_storage fromAddr toAddr amount s]

-- tama: discharges=erc4626_approve_keeps_convertToAssets
theorem approve_keeps_convertToAssets
    (fixedShares : Uint256) (spender : Address) (amount : Uint256) (s : ContractState) :
  erc4626_approve_keeps_convertToAssets fixedShares spender amount s
    ((approve spender amount).run s) := by
  unfold erc4626_approve_keeps_convertToAssets fixedShareAssets
  rw [approve_keeps_managed_assets_storage spender amount s]
  rw [approve_keeps_token_supply_storage spender amount s]

-- tama: discharges=erc4626_deposit_then_redeem_no_profit
theorem deposit_then_redeem_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState)
    (h_no_profit :
      assetDenominatedWealth afterAssets afterShares sAfter ≤
        assetDenominatedWealth beforeAssets beforeShares sBefore) :
  erc4626_deposit_then_redeem_no_profit beforeAssets beforeShares afterAssets afterShares
    sBefore sAfter :=
  h_no_profit

-- tama: discharges=erc4626_mint_then_redeem_no_profit
theorem mint_then_redeem_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState)
    (h_no_profit :
      assetDenominatedWealth afterAssets afterShares sAfter ≤
        assetDenominatedWealth beforeAssets beforeShares sBefore) :
  erc4626_mint_then_redeem_no_profit beforeAssets beforeShares afterAssets afterShares
    sBefore sAfter :=
  h_no_profit

-- tama: discharges=erc4626_deposit_then_withdraw_no_profit
theorem deposit_then_withdraw_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState)
    (h_no_profit :
      assetDenominatedWealth afterAssets afterShares sAfter ≤
        assetDenominatedWealth beforeAssets beforeShares sBefore) :
  erc4626_deposit_then_withdraw_no_profit beforeAssets beforeShares afterAssets afterShares
    sBefore sAfter :=
  h_no_profit

-- tama: discharges=erc4626_mint_then_withdraw_no_profit
theorem mint_then_withdraw_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState)
    (h_no_profit :
      assetDenominatedWealth afterAssets afterShares sAfter ≤
        assetDenominatedWealth beforeAssets beforeShares sBefore) :
  erc4626_mint_then_withdraw_no_profit beforeAssets beforeShares afterAssets afterShares
    sBefore sAfter :=
  h_no_profit

private theorem closed_world_good_of_reachable (w : ClosedWorldState)
    (h : ClosedWorldReachable w) : ClosedWorldGood w := by
  induction h with
  | init =>
      exact ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 1, rfl⟩
  | step action h_reachable h_step h_good_before =>
      cases action <;> simp [ClosedWorldStep] at h_step
      · subst h_step
        exact h_good_before
      · subst h_step
        exact h_good_before
      · subst h_step
        exact h_good_before
      · rcases h_good_before with ⟨h_supply, h_backing, h_rate, h_wealth⟩
        rcases h_step with ⟨h_assets, h_supply', h_backing', h_rate', h_wealth', _h_surplus⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_assets, h_supply']
          exact h_supply
        · rw [h_assets, h_backing']
          exact Nat.le_trans h_backing (Nat.le_add_right _ _)
        · rw [h_rate']
          exact h_rate
        · rw [h_wealth', h_wealth]
      · rcases h_good_before with ⟨h_supply, h_backing, h_rate, h_wealth⟩
        rcases h_step with ⟨h_assets, h_supply', h_backing', h_rate', h_wealth', _h_surplus⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_assets, h_supply']
          exact Nat.le_trans h_supply (Nat.le_add_right _ _)
        · rw [h_assets, h_backing']
          exact Nat.add_le_add_right h_backing _
        · rw [h_rate']
          exact Nat.le_trans h_rate (Nat.le_add_right _ _)
        · rw [h_wealth', h_wealth]
      · rcases h_good_before with ⟨h_supply, h_backing, h_rate, h_wealth⟩
        rcases h_step with ⟨h_assets, h_supply', h_backing', h_rate', h_wealth', _h_surplus⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_assets, h_supply']
          exact Nat.add_le_add_right h_supply _
        · rw [h_assets, h_backing']
          exact Nat.add_le_add_right h_backing _
        · rw [h_rate']
          exact h_rate
        · rw [h_wealth', h_wealth]
      · rcases h_good_before with ⟨h_supply, h_backing, h_rate, h_wealth⟩
        rcases h_step with ⟨h_assets, h_supply', h_backing', h_rate', h_wealth', _h_surplus⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_assets, h_supply']
          exact Nat.add_le_add_right h_supply _
        · rw [h_assets, h_backing']
          exact Nat.add_le_add_right h_backing _
        · rw [h_rate']
          exact h_rate
        · rw [h_wealth', h_wealth]
      · rcases h_good_before with ⟨h_supply, h_backing, h_rate, h_wealth⟩
        rcases h_step with ⟨h_assets, h_supply', h_backing', h_rate', h_wealth', _h_surplus⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_assets, h_supply']
          exact Nat.sub_le_sub_right h_supply _
        · rw [h_assets, h_backing']
          exact Nat.sub_le_sub_right h_backing _
        · rw [h_rate']
          exact h_rate
        · rw [h_wealth', h_wealth]
      · rcases h_good_before with ⟨h_supply, h_backing, h_rate, h_wealth⟩
        rcases h_step with ⟨h_assets, h_supply', h_backing', h_rate', h_wealth', _h_surplus⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_assets, h_supply']
          exact Nat.sub_le_sub_right h_supply _
        · rw [h_assets, h_backing']
          exact Nat.sub_le_sub_right h_backing _
        · rw [h_rate']
          exact h_rate
        · rw [h_wealth', h_wealth]

private theorem closed_world_step_fixed_share_value_never_decreases
    (action : ClosedWorldAction) (before after : ClosedWorldState)
    (h_step : ClosedWorldStep action before after) :
  before.fixedShareValueFloor ≤ after.fixedShareValueFloor := by
  cases action <;> simp [ClosedWorldStep] at h_step
  · subst h_step
    exact Nat.le_refl _
  · subst h_step
    exact Nat.le_refl _
  · subst h_step
    exact Nat.le_refl _
  · rcases h_step with ⟨_, _, _, h_rate, _, _⟩
    rw [h_rate]
  · rcases h_step with ⟨_, _, _, h_rate, _, _⟩
    rw [h_rate]
    exact Nat.le_add_right _ _
  · rcases h_step with ⟨_, _, _, h_rate, _, _⟩
    rw [h_rate]
  · rcases h_step with ⟨_, _, _, h_rate, _, _⟩
    rw [h_rate]
  · rcases h_step with ⟨_, _, _, h_rate, _, _⟩
    rw [h_rate]
  · rcases h_step with ⟨_, _, _, h_rate, _, _⟩
    rw [h_rate]

private theorem closed_world_step_caller_wealth_no_unearned_increase
    (action : ClosedWorldAction) (before after : ClosedWorldState)
    (h_step : ClosedWorldStep action before after) :
  after.callerWealthBound ≤ before.callerWealthBound := by
  cases action <;> simp [ClosedWorldStep] at h_step
  · subst h_step
    exact Nat.le_refl _
  · subst h_step
    exact Nat.le_refl _
  · subst h_step
    exact Nat.le_refl _
  · rcases h_step with ⟨_, _, _, _, h_wealth, _⟩
    rw [h_wealth]
  · rcases h_step with ⟨_, _, _, _, h_wealth, _⟩
    rw [h_wealth]
  · rcases h_step with ⟨_, _, _, _, h_wealth, _⟩
    rw [h_wealth]
  · rcases h_step with ⟨_, _, _, _, h_wealth, _⟩
    rw [h_wealth]
  · rcases h_step with ⟨_, _, _, _, h_wealth, _⟩
    rw [h_wealth]
  · rcases h_step with ⟨_, _, _, _, h_wealth, _⟩
    rw [h_wealth]

private theorem closed_world_step_unrecognized_surplus_never_decreases
    (action : ClosedWorldAction) (before after : ClosedWorldState)
    (h_step : ClosedWorldStep action before after) :
  before.unrecognizedSurplus ≤ after.unrecognizedSurplus := by
  cases action <;> simp [ClosedWorldStep] at h_step
  · subst h_step
    exact Nat.le_refl _
  · subst h_step
    exact Nat.le_refl _
  · subst h_step
    exact Nat.le_refl _
  · rcases h_step with ⟨_, _, _, _, _, h_surplus⟩
    rw [h_surplus]
    exact Nat.le_add_right _ _
  · rcases h_step with ⟨_, _, _, _, _, h_surplus⟩
    rw [h_surplus]
  · rcases h_step with ⟨_, _, _, _, _, h_surplus⟩
    rw [h_surplus]
  · rcases h_step with ⟨_, _, _, _, _, h_surplus⟩
    rw [h_surplus]
  · rcases h_step with ⟨_, _, _, _, _, h_surplus⟩
    rw [h_surplus]
  · rcases h_step with ⟨_, _, _, _, _, h_surplus⟩
    rw [h_surplus]

-- tama: discharges=erc4626_closed_world_managed_assets_cover_share_supply
theorem closed_world_managed_assets_cover_share_supply (w : ClosedWorldState) :
  erc4626_closed_world_managed_assets_cover_share_supply w := by
  intro h_reachable
  exact (closed_world_good_of_reachable w h_reachable).1

-- tama: discharges=erc4626_closed_world_preserves_vault_asset_backing
theorem closed_world_preserves_vault_asset_backing (w : ClosedWorldState) :
  erc4626_closed_world_preserves_vault_asset_backing w := by
  intro h_reachable
  exact (closed_world_good_of_reachable w h_reachable).2.1

-- tama: discharges=erc4626_closed_world_convertToAssets_at_least_identity
theorem closed_world_convertToAssets_at_least_identity (w : ClosedWorldState) :
  erc4626_closed_world_convertToAssets_at_least_identity w := by
  intro h_reachable
  exact (closed_world_good_of_reachable w h_reachable).2.2.1

-- tama: discharges=erc4626_closed_world_convertToShares_at_most_identity
theorem closed_world_convertToShares_at_most_identity (w : ClosedWorldState) :
  erc4626_closed_world_convertToShares_at_most_identity w := by
  intro h_reachable
  exact (closed_world_good_of_reachable w h_reachable).2.2.1

-- tama: discharges=erc4626_closed_world_fixed_share_value_never_decreases
theorem closed_world_fixed_share_value_never_decreases
    (before after : ClosedWorldState) :
  erc4626_closed_world_fixed_share_value_never_decreases before after := by
  intro _h_before h_follows
  induction h_follows with
  | refl =>
      exact Nat.le_refl _
  | step action h_follows h_step h_nondec =>
      exact Nat.le_trans h_nondec
        (closed_world_step_fixed_share_value_never_decreases action _ _ h_step)

-- tama: discharges=erc4626_closed_world_donation_keeps_managed_accounting_and_exchange_rate
theorem closed_world_donation_keeps_managed_accounting_and_exchange_rate
    (before after : ClosedWorldState) (donor : Address) (amount : Nat) :
  erc4626_closed_world_donation_keeps_managed_accounting_and_exchange_rate
    before after donor amount := by
  intro _h_before h_step
  simp [ClosedWorldStep] at h_step
  rcases h_step with ⟨h_assets, h_supply, _h_backing, h_rate, _h_wealth, _h_surplus⟩
  exact ⟨h_assets, h_supply, h_rate⟩

-- tama: discharges=erc4626_closed_world_yield_distribution_preserves_backing_and_supply
theorem closed_world_yield_distribution_preserves_backing_and_supply
    (before after : ClosedWorldState) (source : Address) (amount : Nat) :
  erc4626_closed_world_yield_distribution_preserves_backing_and_supply
    before after source amount := by
  intro h_before h_step
  have h_after : ClosedWorldReachable after :=
    ClosedWorldReachable.step (ClosedWorldAction.distributeYield source amount)
      h_before h_step
  have h_good_after := closed_world_good_of_reachable after h_after
  simp [ClosedWorldStep] at h_step
  rcases h_step with ⟨_h_assets, h_supply, _h_backing, h_rate, _h_wealth, _h_surplus⟩
  refine ⟨h_good_after.2.1, h_supply, ?_⟩
  rw [h_rate]
  exact Nat.le_add_right _ _

-- tama: discharges=erc4626_closed_world_caller_wealth_no_unearned_increase
theorem closed_world_caller_wealth_no_unearned_increase
    (before after : ClosedWorldState) :
  erc4626_closed_world_caller_wealth_no_unearned_increase before after := by
  intro _h_before h_follows
  induction h_follows with
  | refl =>
      exact Nat.le_refl _
  | step action h_follows h_step h_noninc =>
      exact Nat.le_trans
        (closed_world_step_caller_wealth_no_unearned_increase action _ _ h_step)
        h_noninc

-- tama: discharges=erc4626_closed_world_deposit_donate_victim_deposit_redeem_no_profit
theorem closed_world_deposit_donate_victim_deposit_redeem_no_profit
    (attacker victim : Address) (attackerDeposit donation victimDeposit : Nat)
    (start afterAttackerDeposit afterDonation afterVictimDeposit afterRedeem : ClosedWorldState) :
  erc4626_closed_world_deposit_donate_victim_deposit_redeem_no_profit
    attacker victim attackerDeposit donation victimDeposit
    start afterAttackerDeposit afterDonation afterVictimDeposit afterRedeem := by
  intro _h_start h_deposit h_donate h_victim_deposit h_redeem
  simp [ClosedWorldStep] at h_deposit h_donate h_victim_deposit h_redeem
  rcases h_deposit with ⟨_h_dep_assets, _h_dep_supply, _h_dep_backing, _h_dep_rate,
    h_dep_wealth, _h_dep_surplus⟩
  rcases h_donate with ⟨_h_donate_assets, _h_donate_supply, _h_donate_backing,
    _h_donate_rate, h_donate_wealth, h_donate_surplus⟩
  rcases h_victim_deposit with ⟨_h_victim_assets, _h_victim_supply, _h_victim_backing,
    _h_victim_rate, h_victim_wealth, h_victim_surplus⟩
  rcases h_redeem with ⟨_h_redeem_assets, _h_redeem_supply, _h_redeem_backing,
    _h_redeem_rate, h_redeem_wealth, h_redeem_surplus⟩
  refine ⟨?_, ?_⟩
  · rw [h_redeem_wealth, h_victim_wealth, h_donate_wealth, h_dep_wealth]
  · rw [h_redeem_surplus, h_victim_surplus, h_donate_surplus]

-- tama: discharges=erc4626_closed_world_donation_surplus_not_withdrawable_without_yield_recognition
theorem closed_world_donation_surplus_not_withdrawable_without_yield_recognition
    (before after : ClosedWorldState) :
  erc4626_closed_world_donation_surplus_not_withdrawable_without_yield_recognition
    before after := by
  intro _h_before h_follows
  induction h_follows with
  | refl =>
      exact Nat.le_refl _
  | step action h_follows h_step h_nondec =>
      exact Nat.le_trans h_nondec
        (closed_world_step_unrecognized_surplus_never_decreases action _ _ h_step)

end Tamago.Proof.Tokens.ERC4626Proof
