import spec.tokens.ERC4626Spec
import proof.tokens.ERC20Proof
import Verity.Proofs.Stdlib.Automation

namespace proof.tokens.ERC4626Proof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Contracts
open spec.tokens.ERC4626Spec
open src.ERC4626

attribute [local simp] assetToken tokenSupply balances allowances managedAssets
attribute [local simp] src.ERC20.tokenSupply src.ERC20.balances src.ERC20.allowances
attribute [local simp] src.ERC20Base.tokenSupply src.ERC20Base.balances
  src.ERC20Base.allowances src.ERC20Base.maxUint256 src.ERC20Base.decimals
  src.ERC20Base.totalSupply src.ERC20Base.balanceOf src.ERC20Base.allowance
  src.ERC20Base.approve src.ERC20Base.transfer src.ERC20Base.transferFrom
attribute [local simp] src.ERC4626Base.assetToken src.ERC4626Base.tokenSupply
  src.ERC4626Base.balances src.ERC4626Base.allowances src.ERC4626Base.managedAssets
  src.ERC4626Base.maxUint256 src.ERC4626Base.decimals src.ERC4626Base.totalSupply
  src.ERC4626Base.balanceOf src.ERC4626Base.allowance src.ERC4626Base.approve
  src.ERC4626Base.transfer src.ERC4626Base.transferFrom src.ERC4626Base.asset
  src.ERC4626Base.totalAssets src.ERC4626Base.convertToShares
  src.ERC4626Base.convertToAssets src.ERC4626Base.maxDeposit src.ERC4626Base.maxMint
  src.ERC4626Base.maxWithdraw src.ERC4626Base.maxRedeem src.ERC4626Base.previewDeposit
  src.ERC4626Base.previewMint src.ERC4626Base.previewWithdraw src.ERC4626Base.previewRedeem
  src.ERC4626Base.deposit src.ERC4626Base.mint src.ERC4626Base.withdraw
  src.ERC4626Base.redeem Contracts.emit emitEvent

-- tama: discharges=erc4626_decimals_spec
theorem decimals_returns_18 (s : ContractState) :
  erc4626_decimals_spec ((src.ERC4626.decimals).run s).fst := by
  simpa [erc4626_decimals_spec, src.ERC4626.decimals, src.ERC20.decimals]
    using proof.tokens.ERC20Proof.decimals_returns_18 s

-- tama: discharges=erc4626_totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  erc4626_totalSupply_spec ((src.ERC4626.totalSupply).run s).fst s := by
  simpa [erc4626_totalSupply_spec, src.ERC4626.totalSupply, src.ERC20.totalSupply]
    using proof.tokens.ERC20Proof.totalSupply_returns_storage_supply s

-- tama: discharges=erc4626_balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  erc4626_balanceOf_spec account ((src.ERC4626.balanceOf account).run s).fst s := by
  simpa [erc4626_balanceOf_spec, src.ERC4626.balanceOf, src.ERC20.balanceOf]
    using proof.tokens.ERC20Proof.balanceOf_returns_storage_balance account s

-- tama: discharges=erc4626_allowance_spec
theorem allowance_returns_storage_allowance (ownerAddr spender : Address) (s : ContractState) :
  erc4626_allowance_spec ownerAddr spender ((src.ERC4626.allowance ownerAddr spender).run s).fst s := by
  simpa [erc4626_allowance_spec, src.ERC4626.allowance, src.ERC20.allowance]
    using proof.tokens.ERC20Proof.allowance_returns_storage_allowance ownerAddr spender s

-- tama: discharges=erc4626_approve_effect
theorem approve_updates_allowance_only (spender : Address) (amount : Uint256) (s : ContractState) :
  erc4626_approve_effect spender amount s ((src.ERC4626.approve spender amount).run s) := by
  simpa [erc4626_approve_effect, src.ERC4626.approve, src.ERC20.approve]
    using proof.tokens.ERC20Proof.approve_updates_allowance_only spender amount s

-- tama: discharges=erc4626_transfer_balances_effect
theorem transfer_balances_effect_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transfer_balances_effect toAddr amount s ((src.ERC4626.transfer toAddr amount).run s) := by
  simpa [erc4626_transfer_balances_effect, src.ERC4626.transfer, src.ERC20.transfer]
    using proof.tokens.ERC20Proof.transfer_balances_effect_after_run toAddr amount s

-- tama: discharges=erc4626_transferFrom_effect
theorem transferFrom_effect_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  erc4626_transferFrom_effect fromAddr toAddr amount s
    ((src.ERC4626.transferFrom fromAddr toAddr amount).run s) := by
  simpa [erc4626_transferFrom_effect, src.ERC4626.transferFrom, src.ERC20.transferFrom]
    using proof.tokens.ERC20Proof.transferFrom_effect_after_run fromAddr toAddr amount s

-- tama: discharges=erc4626_asset_spec
theorem asset_returns_storage_asset (s : ContractState) :
  erc4626_asset_spec ((asset).run s).fst s := by
  simp [erc4626_asset_spec, asset, assetToken, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_totalAssets_spec
theorem totalAssets_returns_managed_assets (s : ContractState) :
  erc4626_totalAssets_spec ((totalAssets).run s).fst s := by
  simp [erc4626_totalAssets_spec, totalAssets, managedAssets, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_convertToShares_spec
theorem convertToShares_uses_virtual_share_formula (assets : Uint256) (s : ContractState) :
  erc4626_convertToShares_spec assets ((convertToShares assets).run s).fst s := by
  simp [erc4626_convertToShares_spec, convertToShares, managedAssets, tokenSupply,
    getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_convertToAssets_spec
theorem convertToAssets_uses_virtual_share_formula (shares : Uint256) (s : ContractState) :
  erc4626_convertToAssets_spec shares ((convertToAssets shares).run s).fst s := by
  simp [erc4626_convertToAssets_spec, convertToAssets, managedAssets, tokenSupply,
    getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxDeposit_spec
theorem maxDeposit_returns_max_uint256 (receiver : Address) (s : ContractState) :
  erc4626_maxDeposit_spec receiver ((maxDeposit receiver).run s).fst := by
  simp [erc4626_maxDeposit_spec, maxDeposit, maxUint256, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxMint_spec
theorem maxMint_returns_max_uint256 (receiver : Address) (s : ContractState) :
  erc4626_maxMint_spec receiver ((maxMint receiver).run s).fst := by
  simp [erc4626_maxMint_spec, maxMint, maxUint256, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxWithdraw_spec
theorem maxWithdraw_returns_convertible_owner_assets (ownerAddr : Address) (s : ContractState) :
  erc4626_maxWithdraw_spec ownerAddr ((maxWithdraw ownerAddr).run s).fst s := by
  simp [erc4626_maxWithdraw_spec, maxWithdraw, managedAssets, tokenSupply, balances,
    getMapping, getStorage, Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_maxRedeem_spec
theorem maxRedeem_returns_owner_shares (ownerAddr : Address) (s : ContractState) :
  erc4626_maxRedeem_spec ownerAddr ((maxRedeem ownerAddr).run s).fst s := by
  simp [erc4626_maxRedeem_spec, maxRedeem, balances, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewDeposit_spec
theorem previewDeposit_matches_convertToShares (assets : Uint256) (s : ContractState) :
  erc4626_previewDeposit_spec assets ((previewDeposit assets).run s).fst s := by
  simp [erc4626_previewDeposit_spec, erc4626_convertToShares_spec, previewDeposit,
    convertToShares, managedAssets, tokenSupply, getStorage, Contract.run, Verity.bind,
    Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewMint_spec
theorem previewMint_rounds_assets_up (shares : Uint256) (s : ContractState) :
  erc4626_previewMint_spec shares ((previewMint shares).run s).fst s := by
  simp [erc4626_previewMint_spec, previewMint, managedAssets, tokenSupply, getStorage, Contract.run,
    Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewWithdraw_spec
theorem previewWithdraw_rounds_shares_up (assets : Uint256) (s : ContractState) :
  erc4626_previewWithdraw_spec assets ((previewWithdraw assets).run s).fst s := by
  simp [erc4626_previewWithdraw_spec, previewWithdraw, managedAssets, tokenSupply, getStorage,
    Contract.run, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_previewRedeem_spec
theorem previewRedeem_matches_convertToAssets (shares : Uint256) (s : ContractState) :
  erc4626_previewRedeem_spec shares ((previewRedeem shares).run s).fst s := by
  simp [erc4626_previewRedeem_spec, erc4626_convertToAssets_spec, previewRedeem,
    convertToAssets, managedAssets, tokenSupply, getStorage, Contract.run, Verity.bind,
    Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=erc4626_deposit_effect
theorem deposit_mints_shares_and_tracks_assets
    (assets : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_deposit_effect assets receiver s ((deposit assets receiver).run s) := by
  unfold erc4626_deposit_effect
  refine ⟨?_, ?_⟩
  · intro h_balance_overflow
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 2 receiver).val +
            (div (mul assets (add (s.storage 1) 1)) (add (s.storage 4) 1)).val := by
      simpa using h_balance_overflow
    simp [deposit, assetToken, balances, tokenSupply, managedAssets, msgSender,
      common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, safeTransferFrom,
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
        common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, safeTransferFrom,
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
          common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, setMapping,
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
            common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, setMapping,
            setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
            Verity.pure, Pure.pure]

-- tama: discharges=erc4626_mint_effect
theorem mint_mints_shares_and_tracks_assets
    (shares : Uint256) (receiver : Address) (s : ContractState) :
  erc4626_mint_effect shares receiver s ((mint shares receiver).run s) := by
  unfold erc4626_mint_effect
  refine ⟨?_, ?_⟩
  · intro h_balance_overflow
    have h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
      simpa using h_balance_overflow
    simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
      common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, safeTransferFrom,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_overflow,
      Verity.pure, Pure.pure]
  · intro h_balance_no_overflow
    have h_balance_no_overflow_raw :
        (s.storageMap 2 receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa using h_balance_no_overflow
    have h_not_balance_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 2 receiver).val + shares.val := by
      omega
    refine ⟨?_, ?_⟩
    · intro h_supply_overflow
      have h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by
        simpa using h_supply_overflow
      simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
        common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, safeTransferFrom,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_not_balance_overflow, h_overflow, Verity.pure, Pure.pure]
    · intro h_supply_no_overflow
      have h_supply_no_overflow_raw :
          (s.storage 1).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa using h_supply_no_overflow
      have h_not_supply_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storage 1).val + shares.val := by omega
      refine ⟨?_, ?_⟩
      · intro h_assets_overflow
        have h_overflow :
            Verity.Stdlib.Math.MAX_UINT256 <
              (s.storage 4).val +
                (div
                  (add (mul shares (add (s.storage 4) 1))
                    (sub (add (s.storage 1) 1) 1))
                  (add (s.storage 1) 1)).val := by
          simpa using h_assets_overflow
        simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
          common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, setMapping,
          setStorage, safeTransferFrom, Contract.run, ContractResult.snd, Verity.bind,
          Bind.bind, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_not_balance_overflow, h_not_supply_overflow,
          h_overflow, Verity.pure, Pure.pure]
      · intro h_assets_no_overflow
        have h_assets_no_overflow_raw :
            (s.storage 4).val +
                (div
                  (add (mul shares (add (s.storage 4) 1))
                    (sub (add (s.storage 1) 1) 1))
                  (add (s.storage 1) 1)).val ≤
              Verity.Stdlib.Math.MAX_UINT256 := by
          simpa using h_assets_no_overflow
        have h_not_assets_overflow :
            ¬ Verity.Stdlib.Math.MAX_UINT256 <
              (s.storage 4).val +
                (div
                  (add (mul shares (add (s.storage 4) 1))
                    (sub (add (s.storage 1) 1) 1))
                  (add (s.storage 1) 1)).val := by
          omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [mint, assetToken, balances, tokenSupply, managedAssets, msgSender,
            common.ECM.selfAddressModule, Verity.wordToAddress, getStorageAddr, getStorage, getMapping, setMapping,
            setStorage, safeTransferFrom, mstore, rawLog, emitEvent,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            h_not_balance_overflow, h_not_supply_overflow, h_not_assets_overflow,
            Verity.pure, Pure.pure]

-- tama: discharges=erc4626_withdraw_effect
theorem withdraw_burns_shares_and_sends_assets
    (assets : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_withdraw_effect assets receiver ownerAddr s ((withdraw assets receiver ownerAddr).run s) := by
  unfold erc4626_withdraw_effect
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

-- tama: discharges=erc4626_redeem_effect
theorem redeem_burns_shares_and_sends_assets
    (shares : Uint256) (receiver ownerAddr : Address) (s : ContractState) :
  erc4626_redeem_effect shares receiver ownerAddr s ((redeem shares receiver ownerAddr).run s) := by
  unfold erc4626_redeem_effect
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

end proof.tokens.ERC4626Proof
