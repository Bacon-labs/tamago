import Tamago.Spec.Utils.SafeTransferLibSpec
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Utils.SafeTransferLibProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open Tamago.Utils.SafeTransferLib
open Tamago.Spec.Utils.SafeTransferLibSpec

attribute [local simp] transfer transferFrom approve
  Tamago.Utils.SafeTransferLibBase.transfer
  Tamago.Utils.SafeTransferLibBase.transferFrom
  Tamago.Utils.SafeTransferLibBase.approve
  Contracts.safeTransfer Contracts.safeTransferFrom Contracts.safeApprove

-- tama: discharges=safeTransferLib_transfer_returns_true
theorem transfer_returns_true
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
    safeTransferLib_transfer_returns_true token toAddr amount s
      ((transfer token toAddr amount).run s) := by
  simp [safeTransferLib_transfer_returns_true, Contract.run,
    Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=safeTransferLib_transfer_keeps_storage
theorem transfer_keeps_storage
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
    safeTransferLib_transfer_keeps_storage token toAddr amount s
      ((transfer token toAddr amount).run s) := by
  simp [safeTransferLib_transfer_keeps_storage, Contract.run,
    ContractResult.snd, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=safeTransferLib_transferFrom_returns_true
theorem transferFrom_returns_true
    (token fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
    safeTransferLib_transferFrom_returns_true token fromAddr toAddr amount s
      ((transferFrom token fromAddr toAddr amount).run s) := by
  simp [safeTransferLib_transferFrom_returns_true, Contract.run,
    Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=safeTransferLib_transferFrom_keeps_storage
theorem transferFrom_keeps_storage
    (token fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
    safeTransferLib_transferFrom_keeps_storage token fromAddr toAddr amount s
      ((transferFrom token fromAddr toAddr amount).run s) := by
  simp [safeTransferLib_transferFrom_keeps_storage, Contract.run,
    ContractResult.snd, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=safeTransferLib_approve_returns_true
theorem approve_returns_true
    (token spender : Address) (amount : Uint256) (s : ContractState) :
    safeTransferLib_approve_returns_true token spender amount s
      ((approve token spender amount).run s) := by
  simp [safeTransferLib_approve_returns_true, Contract.run,
    Verity.bind, Verity.pure, Bind.bind, Pure.pure]

-- tama: discharges=safeTransferLib_approve_keeps_storage
theorem approve_keeps_storage
    (token spender : Address) (amount : Uint256) (s : ContractState) :
    safeTransferLib_approve_keeps_storage token spender amount s
      ((approve token spender amount).run s) := by
  simp [safeTransferLib_approve_keeps_storage, Contract.run,
    ContractResult.snd, Verity.bind, Verity.pure, Bind.bind, Pure.pure]

end Tamago.Proof.Utils.SafeTransferLibProof
