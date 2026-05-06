import spec.ERC20LiteSpec
import Verity.Proofs.Stdlib.Automation

namespace proof.ERC20LiteProof

open Verity
open Verity.EVM.Uint256
open spec.ERC20LiteSpec
open src.ERC20Lite

-- Each `tama: discharges=` comment binds a proof theorem to a spec; the spec
-- in turn is mirrored by a Foundry test (or listed under
-- `[coverage.proof_only]` in `tama.toml`).
-- tama: discharges=mint_owner_preserved
theorem mint_preserves_owner_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  let s' := ((mint toAddr amount).run s).snd
  mint_owner_preserved s s' := by
  unfold mint_owner_preserved
  by_cases h_owner : s.sender = s.storageAddr 0
  · simp [mint, ownerSlot, balancesSlot, totalSupplySlot, msgSender, getStorageAddr,
      getMapping, getStorage, setMapping, setStorage, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
      Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd, h_owner]
    by_cases h_balance_overflow : Verity.Stdlib.Math.MAX_UINT256 <
        (s.storageMap 1 toAddr).val + amount.val
    · simp [h_balance_overflow, Verity.require, Verity.bind]
    · by_cases h_supply_overflow : Verity.Stdlib.Math.MAX_UINT256 <
          (s.storage 2).val + amount.val <;>
        simp [h_balance_overflow, h_supply_overflow, Verity.require, Verity.bind,
          Verity.pure]
  · simp [mint, ownerSlot, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_owner]

-- tama: discharges=transfer_total_supply_preserved
theorem transfer_total_supply_preserved_after_run (toAddr : Address) (amount : Uint256) (s : ContractState) :
  let s' := ((transfer toAddr amount).run s).snd
  transfer_total_supply_preserved s s' := by
  unfold transfer_total_supply_preserved
  by_cases h_balance : amount.val ≤ (s.storageMap 1 s.sender).val
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Pure.pure,
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

-- Successful-path effect for `transfer`. The proof case-splits on
-- self-transfer to discharge the spec's two branches: in the self-transfer
-- branch the contract takes the `pure ()` shortcut and the storageMap is
-- untouched; in the non-self branch the simp set unfolds `safeAdd` under
-- `h_not_overflow_strict` and the if-then-else inside the storageMap
-- closure resolves to `sub` and the recipient credit. The `show` step in
-- the sender debit goal rewrites `s' - amount` into the `sub s'` form that
-- `setMapping` literally produces — they are definitionally equal via the
-- HSub instance, but simp on `+` fires `add_comm` while `sub` is left
-- alone, so the two sides need to be brought into the same shape by hand.
-- tama: discharges=transfer_balances_effect
theorem transfer_balances_effect_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  transfer_balances_effect toAddr amount s ((transfer toAddr amount).run s).snd := by
  unfold transfer_balances_effect
  intro h_balance
  refine ⟨?_, ?_⟩
  · -- Self-transfer branch: `pure ()` shortcut leaves the balance unchanged.
    -- `subst` rewrites `toAddr` to `s.sender` everywhere so `h_balance`
    -- discharges the `senderBalance >= amount` require directly.
    intro h_eq
    subst h_eq
    simp [transfer, balancesSlot, msgSender, getMapping,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Verity.require, h_balance]
  · -- Non-self branch: full debit/credit under no-overflow.
    intro h_ne h_no_overflow
    have h_not_overflow_strict :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 1 toAddr).val + amount.val := by omega
    refine ⟨?_, ?_⟩
    · show ((transfer toAddr amount).run s).snd.storageMap 1 s.sender =
        sub (s.storageMap 1 s.sender) amount
      simp [transfer, balancesSlot, msgSender, getMapping, setMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_balance, h_ne, h_not_overflow_strict]
    · simp [transfer, balancesSlot, msgSender, getMapping, setMapping,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_balance, h_ne, h_not_overflow_strict]

-- tama: discharges=balanceOf_spec
theorem balanceOf_returns_storage_balance (account : Address) (s : ContractState) :
  let result := ((balanceOf account).run s).fst
  balanceOf_spec account result s := by
  simp [balanceOf_spec, balanceOf, balancesSlot, Bind.bind, Pure.pure]

-- tama: discharges=totalSupply_spec
theorem totalSupply_returns_storage_supply (s : ContractState) :
  let result := ((totalSupply).run s).fst
  totalSupply_spec result s := by
  simp [totalSupply_spec, totalSupply, totalSupplySlot, Bind.bind, Pure.pure]

-- tama: discharges=owner_spec
theorem owner_returns_storage_owner (s : ContractState) :
  let result := ((owner).run s).fst
  owner_spec result s := by
  simp [owner_spec, owner, ownerSlot, Bind.bind, Pure.pure]

-- Negative access control: when the caller is not the owner, `mint` reverts,
-- and a revert carries the original state unchanged. Specs whose body is an
-- implication are stated without `let s'` so `intro` reaches the antecedent
-- directly (a `let` binder would otherwise be the first thing introduced).
-- tama: discharges=mint_unauthorized_no_change
theorem mint_unauthorized_no_change_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  mint_unauthorized_no_change toAddr amount s ((mint toAddr amount).run s).snd := by
  unfold mint_unauthorized_no_change
  intro h_not_owner
  refine ⟨?_, ?_⟩ <;>
    simp [mint, ownerSlot, msgSender, getStorageAddr, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_not_owner]

-- Authorized-path effect: when sender = owner, `transferOwnership` writes the
-- new owner into slot 0. The single-branch proof is the simplest shape — no
-- case split, just unfold and let `setStorageAddr` rewrite the slot.
-- tama: discharges=transferOwnership_authorized_sets_owner
theorem transferOwnership_authorized_sets_owner_after_run
    (newOwner : Address) (s : ContractState) :
  transferOwnership_authorized_sets_owner newOwner s
    ((transferOwnership newOwner).run s).snd := by
  unfold transferOwnership_authorized_sets_owner
  intro h_owner
  simp [transferOwnership, ownerSlot, msgSender, getStorageAddr, setStorageAddr,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
    Verity.require, h_owner]

-- Negative access control: a non-owner caller leaves slot 0 untouched.
-- tama: discharges=transferOwnership_unauthorized_owner_unchanged
theorem transferOwnership_unauthorized_owner_unchanged_after_run
    (newOwner : Address) (s : ContractState) :
  transferOwnership_unauthorized_owner_unchanged s
    ((transferOwnership newOwner).run s).snd := by
  unfold transferOwnership_unauthorized_owner_unchanged
  intro h_not_owner
  simp [transferOwnership, ownerSlot, msgSender, getStorageAddr,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
    Verity.require, h_not_owner]

-- Frame condition: `transferOwnership` never touches the totalSupply slot.
-- The proof case-splits on authorization so the same statement covers both
-- branches — the authorized branch does write a slot, just not slot 2.
-- tama: discharges=transferOwnership_supply_preserved
theorem transferOwnership_supply_preserved_after_run
    (newOwner : Address) (s : ContractState) :
  let s' := ((transferOwnership newOwner).run s).snd
  transferOwnership_supply_preserved s s' := by
  unfold transferOwnership_supply_preserved
  by_cases h_owner : s.sender = s.storageAddr 0
  · simp [transferOwnership, ownerSlot, msgSender, getStorageAddr, setStorageAddr,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, h_owner]
  · simp [transferOwnership, ownerSlot, msgSender, getStorageAddr,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, h_owner]

-- Frame condition: `transferOwnership` never touches the balances mapping.
-- tama: discharges=transferOwnership_balances_preserved
theorem transferOwnership_balances_preserved_after_run
    (account : Address) (newOwner : Address) (s : ContractState) :
  let s' := ((transferOwnership newOwner).run s).snd
  transferOwnership_balances_preserved account s s' := by
  unfold transferOwnership_balances_preserved
  by_cases h_owner : s.sender = s.storageAddr 0
  · simp [transferOwnership, ownerSlot, msgSender, getStorageAddr,
      setStorageAddr, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, h_owner]
  · simp [transferOwnership, ownerSlot, msgSender, getStorageAddr,
      Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.require, h_owner]

end proof.ERC20LiteProof
