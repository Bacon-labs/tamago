import Contracts.Common

namespace Tamago.Utils

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256

/-
@title SafeTransferLib
@notice Tamago wrappers around the Verity stdlib's ERC-20 safe-call ECMs.
The contract functions `transfer`, `transferFrom`, and `approve` forward to
the underlying ECMs (selectors `0xa9059cbb`, `0x23b872dd`, `0x095ea7b3`)
with the standard "optional-bool" guard: the target is allowed to either
return no data when it has code (the USDT pattern) or return data whose
first 32 bytes equal ABI-encoded `true`. A returned `false`, an EVM revert,
or a call to a no-code address all revert the wrapper. The guard reads only
the first 32 bytes of the return area, so longer returns are accepted as
long as their first word is `1`; short returns combined with stale calldata
in the output buffer are a known boundary that mirror tests in
`test/verity/utils/SafeTransferLib.t.sol` document explicitly.
@dev Tamago consumers normally inline the Lean-side helpers
`Contracts.safeTransfer` / `Contracts.safeTransferFrom` / `Contracts.safeApprove`
into their own `verity_contract`s — the deployable contract surfaced here is
primarily a Foundry-side test target so the EVM-level safety of the underlying
Yul codegen can be exercised against pathological tokens (no-return-bool,
false-return, no-code address, oversized return, reverting, fee-on-transfer,
ERC-777 hook, rebasing) in mirror tests.
The function names use the unwrapped form (`transfer` etc.) because the
Verity macro reserves `safeTransfer` / `safeTransferFrom` / `safeApprove` as
intrinsic ECM-emitting syntax forms; a deployable contract cannot expose
those names without colliding with the macro. Solidity callers see the
behaviour as "SafeTransferLib.transfer(token, to, amount)".
-/
verity_contract SafeTransferLibBase where
  storage

  /-
  @notice Forwards `transfer(toAddr, amount)` to `token` with optional-bool
  handling: accepts no return data when the target has code, or any return
  whose first 32 bytes equal `true`.
  @return True on accepted success; the call reverts on EVM revert, returned
  false, or a no-code target.
  -/
  function transfer (token : Address, toAddr : Address, amount : Uint256) : Bool := do
    safeTransfer token toAddr amount
    return true

  /-
  @notice Forwards `transferFrom(fromAddr, toAddr, amount)` to `token` with
  optional-bool handling.
  @return True on accepted success.
  -/
  function transferFrom
      (token : Address, fromAddr : Address, toAddr : Address, amount : Uint256) : Bool := do
    safeTransferFrom token fromAddr toAddr amount
    return true

  /-
  @notice Forwards `approve(spender, amount)` to `token` with optional-bool
  handling.
  @return True on accepted success.
  @dev Note: the underlying `approve` race condition is unchanged by this
  wrapper. Production consumers should prefer increase/decrease-allowance
  patterns or zero-then-set flows when supported by the target token.
  -/
  function approve (token : Address, spender : Address, amount : Uint256) : Bool := do
    safeApprove token spender amount
    return true

namespace SafeTransferLib

abbrev transfer := SafeTransferLibBase.transfer
abbrev transferFrom := SafeTransferLibBase.transferFrom
abbrev approve := SafeTransferLibBase.approve

def spec : Compiler.CompilationModel.CompilationModel :=
  { SafeTransferLibBase.spec with
    name := "SafeTransferLib" }

end SafeTransferLib

end Tamago.Utils
