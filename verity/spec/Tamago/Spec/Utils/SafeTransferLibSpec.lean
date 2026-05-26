import Tamago.Utils.SafeTransferLib

namespace Tamago.Spec.Utils.SafeTransferLibSpec

open Verity
open Verity.EVM.Uint256
open Tamago.Utils.SafeTransferLib

/-
SafeTransferLib specs are about the wrapper-contract behavior on the Lean
modeling layer where the underlying ERC-20 ECMs (`Contracts.safeTransfer*`)
are total functions that return `pure ()`. The substantive EVM-level safety
of those ECMs — optional-bool acceptance, no-code rejection, returned-false
rejection, oversized-return rejection — is owned by Verity's compilation-
correctness theorem for the Yul codegen and is exercised end-to-end by the
Foundry mirror tests in `test/verity/utils/SafeTransferLib.t.sol`.

At this layer the proofs simply confirm that the Tamago wrappers do not add
any spurious storage writes or non-trivial control flow beyond forwarding to
the ECM and returning `true`.
-/

/-
transfer(token, toAddr, amount)

Properties specified:
- The wrapper returns `true` whenever the underlying ECM completes (which,
  at the Lean modeling layer, is always — production EVM reverts are
  modeled by Verity's compilation-correctness theorem, not at this layer).
- The wrapper does not touch its own storage, address-storage, or any of
  the mapping/array storage facets.

Security conclusions:
- The wrapper has no internal state it could corrupt.
- A consumer that calls `transfer` cannot accidentally cause the
  library contract to write to one of its own slots.
-/
def safeTransferLib_transfer_returns_true
    (_token _toAddr : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true s

def safeTransferLib_transfer_keeps_storage
    (_token _toAddr : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage ∧
    result.snd.storageAddr = s.storageAddr ∧
    result.snd.storageMap = s.storageMap ∧
    result.snd.storageMap2 = s.storageMap2 ∧
    result.snd.storageArray = s.storageArray ∧
    result.snd.storageMapUint = s.storageMapUint

/-
transferFrom(token, fromAddr, toAddr, amount)

Properties specified:
- Identical wrapper-discipline properties as `transfer`.
-/
def safeTransferLib_transferFrom_returns_true
    (_token _fromAddr _toAddr : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true s

def safeTransferLib_transferFrom_keeps_storage
    (_token _fromAddr _toAddr : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage ∧
    result.snd.storageAddr = s.storageAddr ∧
    result.snd.storageMap = s.storageMap ∧
    result.snd.storageMap2 = s.storageMap2 ∧
    result.snd.storageArray = s.storageArray ∧
    result.snd.storageMapUint = s.storageMapUint

/-
approve(token, spender, amount)

Properties specified:
- Identical wrapper-discipline properties as `transfer`.
-/
def safeTransferLib_approve_returns_true
    (_token _spender : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true s

def safeTransferLib_approve_keeps_storage
    (_token _spender : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage ∧
    result.snd.storageAddr = s.storageAddr ∧
    result.snd.storageMap = s.storageMap ∧
    result.snd.storageMap2 = s.storageMap2 ∧
    result.snd.storageArray = s.storageArray ∧
    result.snd.storageMapUint = s.storageMapUint

end Tamago.Spec.Utils.SafeTransferLibSpec
