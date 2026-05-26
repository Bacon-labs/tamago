import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FinCases
import Mathlib.Tactic
import Tamago.Utils.FixedPointMathLib

namespace Tamago.Proof.Utils.ClzProof

open Verity
open Verity.EVM.Uint256
open Tamago.Utils
open Tamago.Utils.FixedPointMathLib

private def clzScanStepNat (x r shift : Nat) : Nat :=
  if 2 ^ shift - 1 < x / 2 ^ r then r + shift else r

private def clzScanNat (x : Nat) : Nat :=
  let r := clzScanStepNat x 0 128
  let r := clzScanStepNat x r 64
  let r := clzScanStepNat x r 32
  let r := clzScanStepNat x r 16
  clzScanStepNat x r 8

private def clzScanLogStep (k r shift : Nat) : Nat :=
  if r + shift ≤ k then r + shift else r

private def clzScanLog (k : Nat) : Nat :=
  let r := clzScanLogStep k 0 128
  let r := clzScanLogStep k r 64
  let r := clzScanLogStep k r 32
  let r := clzScanLogStep k r 16
  clzScanLogStep k r 8

private theorem pow_two_le_iff_le_log2 {x e : Nat} (hx : x ≠ 0) :
    2 ^ e ≤ x ↔ e ≤ Nat.log2 x := by
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_le_iff_le_log (by decide : 1 < 2) hx

private theorem clzScanStepNat_eq_logStep
    (x r shift : Nat) (hx : x ≠ 0) :
    clzScanStepNat x r shift = clzScanLogStep (Nat.log2 x) r shift := by
  unfold clzScanStepNat clzScanLogStep
  have hpow : 0 < 2 ^ r := Nat.pow_pos (by decide : 0 < 2)
  have hbranch :
      (2 ^ shift - 1 < x / 2 ^ r) ↔ r + shift ≤ Nat.log2 x := by
    calc
      2 ^ shift - 1 < x / 2 ^ r
          ↔ 2 ^ shift ≤ x / 2 ^ r := by
              have hshiftPow : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
              omega
      _ ↔ 2 ^ shift * 2 ^ r ≤ x :=
          Nat.le_div_iff_mul_le hpow
      _ ↔ 2 ^ (r + shift) ≤ x := by
          rw [Nat.pow_add, Nat.mul_comm]
      _ ↔ r + shift ≤ Nat.log2 x :=
          pow_two_le_iff_le_log2 hx
  by_cases h : r + shift ≤ Nat.log2 x
  · rw [if_pos (hbranch.mpr h), if_pos h]
  · rw [if_neg (fun hb => h (hbranch.mp hb)), if_neg h]

private theorem clzScanNat_eq_logScan (x : Nat) (hx : x ≠ 0) :
    clzScanNat x = clzScanLog (Nat.log2 x) := by
  unfold clzScanNat clzScanLog
  simp [clzScanStepNat_eq_logStep x _ _ hx]

private theorem clzScanLog_eq_byte_floor (k : Nat) (hk : k < 256) :
    clzScanLog k = 8 * (k / 8) := by
  interval_cases k <;> native_decide

private theorem clzScanNat_eq_byte_floor
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    clzScanNat x = 8 * (Nat.log2 x / 8) := by
  rw [clzScanNat_eq_logScan x hx]
  exact clzScanLog_eq_byte_floor (Nat.log2 x) ((Nat.log2_lt hx).2 hx256)

private theorem clzScanNat_le_log2
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    clzScanNat x ≤ Nat.log2 x := by
  rw [clzScanNat_eq_byte_floor x hx hx256]
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (Nat.log2 x) 8

private theorem log2_lt_clzScanNat_add_eight
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    Nat.log2 x < clzScanNat x + 8 := by
  rw [clzScanNat_eq_byte_floor x hx hx256]
  have hmod : Nat.log2 x % 8 < 8 := Nat.mod_lt _ (by decide : 0 < 8)
  have hdecomp : 8 * (Nat.log2 x / 8) + Nat.log2 x % 8 = Nat.log2 x := by
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.div_add_mod (Nat.log2 x) 8
  omega

private theorem clzScanNat_le_248
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    clzScanNat x ≤ 248 := by
  rw [clzScanNat_eq_byte_floor x hx hx256]
  have hlog : Nat.log2 x < 256 := (Nat.log2_lt hx).2 hx256
  have hdiv : Nat.log2 x / 8 ≤ 31 := by omega
  omega

private theorem clzScanNat_mod_eight
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    clzScanNat x % 8 = 0 := by
  rw [clzScanNat_eq_byte_floor x hx hx256]
  exact Nat.mul_mod_right 8 (Nat.log2 x / 8)

private theorem clzWindow_pos
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    0 < x / 2 ^ clzScanNat x := by
  have hscan := clzScanNat_le_log2 x hx hx256
  have hpow : 2 ^ clzScanNat x ≤ x := by
    exact (pow_two_le_iff_le_log2 hx).2 hscan
  exact Nat.div_pos hpow (Nat.pow_pos (by decide : 0 < 2))

private theorem clzWindow_lt_256
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    x / 2 ^ clzScanNat x < 256 := by
  have hlog := log2_lt_clzScanNat_add_eight x hx hx256
  have hxlt : x < 2 ^ (clzScanNat x + 8) := by
    have hlog' : Nat.log 2 x < clzScanNat x + 8 := by
      simpa [Nat.log2_eq_log_two] using hlog
    exact Nat.lt_pow_of_log_lt (by decide : 1 < 2) hlog'
  have hpow :
      2 ^ clzScanNat x * 256 = 2 ^ (clzScanNat x + 8) := by
    change 2 ^ clzScanNat x * 2 ^ 8 = 2 ^ (clzScanNat x + 8)
    rw [Nat.pow_add]
  have hdiv : x / 2 ^ clzScanNat x < 2 ^ 8 :=
    Nat.div_lt_of_lt_mul (by simpa [hpow] using hxlt)
  simpa using hdiv

private theorem log2_clzWindow
    (x : Nat) (hx : x ≠ 0) (hx256 : x < 2 ^ 256) :
    Nat.log2 (x / 2 ^ clzScanNat x) = Nat.log2 x - clzScanNat x := by
  let r := clzScanNat x
  let k := Nat.log2 x
  have hrk : r ≤ k := by
    simpa [r, k] using clzScanNat_le_log2 x hx hx256
  have hpowLower : 2 ^ k ≤ x := by
    simpa [Nat.log2_eq_log_two, k] using Nat.pow_log_le_self 2 hx
  have hlow : 2 ^ (k - r) ≤ x / 2 ^ r := by
    have hmul : 2 ^ (k - r) * 2 ^ r ≤ x := by
      have hsum : k - r + r = k := by omega
      have hpowEq : 2 ^ (k - r) * 2 ^ r = 2 ^ k := by
        rw [← Nat.pow_add, hsum]
      simpa [hpowEq] using hpowLower
    exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 2))).2 hmul
  have hpowUpper : x < 2 ^ (k + 1) := by
    simpa [Nat.log2_eq_log_two, k, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
  have hup : x / 2 ^ r < 2 ^ (k - r + 1) := by
    have hmulEq : 2 ^ (k - r + 1) * 2 ^ r = 2 ^ (k + 1) := by
      have hsum : k - r + 1 + r = k + 1 := by omega
      rw [← Nat.pow_add, hsum]
    exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))).2
      (by simpa [hmulEq] using hpowUpper)
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow hlow hup

private theorem shr_val (shift value : Uint256) :
    (shr shift value).val = value.val / 2 ^ shift.val := by
  have hLt : value.val / 2 ^ shift.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) value.isLt
  simp [shr, Verity.Core.Uint256.shr, Verity.Core.Uint256.ofNat,
    Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt hLt

@[simp] private theorem clzThreshold128_val :
    (0xffffffffffffffffffffffffffffffff : Uint256).val = 2 ^ 128 - 1 := by
  native_decide

@[simp] private theorem clzThreshold64_val :
    (0xffffffffffffffff : Uint256).val = 2 ^ 64 - 1 := by
  native_decide

@[simp] private theorem clzThreshold32_val :
    (0xffffffff : Uint256).val = 2 ^ 32 - 1 := by
  native_decide

@[simp] private theorem clzThreshold16_val :
    (0xffff : Uint256).val = 2 ^ 16 - 1 := by
  native_decide

@[simp] private theorem clzThreshold8_val :
    (0xff : Uint256).val = 2 ^ 8 - 1 := by
  native_decide

private def clzScanUint (x : Uint256) : Uint256 :=
  let r := shl 7 (boolToWord (0xffffffffffffffffffffffffffffffff < x))
  let r := Contracts.bitOr r (shl 6 (boolToWord (0xffffffffffffffff < shr r x)))
  let r := Contracts.bitOr r (shl 5 (boolToWord (0xffffffff < shr r x)))
  let r := Contracts.bitOr r (shl 4 (boolToWord (0xffff < shr r x)))
  Contracts.bitOr r (shl 3 (boolToWord (0xff < shr r x)))

private theorem clzScanStepUint_val
    (x rU bitShift threshold : Uint256) (rn shift : Nat)
    (hr : rU.val = rn)
    (hThreshold : threshold.val = 2 ^ shift - 1)
    (hTrue :
      (Contracts.bitOr rU (shl bitShift (boolToWord true))).val = rn + shift)
    (hFalse :
      (Contracts.bitOr rU (shl bitShift (boolToWord false))).val = rn) :
    (Contracts.bitOr rU (shl bitShift (boolToWord (threshold < shr rU x)))).val =
      clzScanStepNat x.val rn shift := by
  unfold clzScanStepNat
  have hBranch :
      (threshold < shr rU x) ↔ 2 ^ shift - 1 < x.val / 2 ^ rn := by
    change threshold.val < (shr rU x).val ↔ 2 ^ shift - 1 < x.val / 2 ^ rn
    rw [shr_val, hr, hThreshold]
  by_cases h : 2 ^ shift - 1 < x.val / 2 ^ rn
  · have hUint := hBranch.mpr h
    simp [hUint, h]
    simpa [boolToWord] using hTrue
  · have hUint : ¬ threshold < shr rU x := fun hh => h (hBranch.mp hh)
    simp [hUint, h]
    simpa [boolToWord] using hFalse

private theorem clzScanStepNat_128_possible (x : Nat) :
    clzScanStepNat x 0 128 = 0 ∨ clzScanStepNat x 0 128 = 128 := by
  unfold clzScanStepNat
  split <;> omega

private theorem clzScanStepNat_64_possible
    (x rn : Nat) (hrn : rn = 0 ∨ rn = 128) :
    clzScanStepNat x rn 64 = 0 ∨ clzScanStepNat x rn 64 = 128 ∨
      clzScanStepNat x rn 64 = 64 ∨ clzScanStepNat x rn 64 = 192 := by
  unfold clzScanStepNat
  rcases hrn with rfl | rfl
  all_goals split <;> omega

private theorem clzScanStepNat_32_possible
    (x rn : Nat)
    (hrn : rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192) :
    clzScanStepNat x rn 32 = 0 ∨ clzScanStepNat x rn 32 = 128 ∨
      clzScanStepNat x rn 32 = 64 ∨ clzScanStepNat x rn 32 = 192 ∨
        clzScanStepNat x rn 32 = 32 ∨ clzScanStepNat x rn 32 = 160 ∨
          clzScanStepNat x rn 32 = 96 ∨ clzScanStepNat x rn 32 = 224 := by
  unfold clzScanStepNat
  rcases hrn with rfl | rfl | rfl | rfl
  all_goals split <;> omega

private theorem clzScanStepNat_16_possible
    (x rn : Nat)
    (hrn :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224) :
    clzScanStepNat x rn 16 = 0 ∨ clzScanStepNat x rn 16 = 128 ∨
      clzScanStepNat x rn 16 = 64 ∨ clzScanStepNat x rn 16 = 192 ∨
        clzScanStepNat x rn 16 = 32 ∨ clzScanStepNat x rn 16 = 160 ∨
          clzScanStepNat x rn 16 = 96 ∨ clzScanStepNat x rn 16 = 224 ∨
            clzScanStepNat x rn 16 = 16 ∨ clzScanStepNat x rn 16 = 144 ∨
              clzScanStepNat x rn 16 = 80 ∨ clzScanStepNat x rn 16 = 208 ∨
                clzScanStepNat x rn 16 = 48 ∨ clzScanStepNat x rn 16 = 176 ∨
                  clzScanStepNat x rn 16 = 112 ∨ clzScanStepNat x rn 16 = 240 := by
  unfold clzScanStepNat
  rcases hrn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals split <;> omega

private theorem bitOr_shl_6_true_val
    (rU : Uint256) {rn : Nat} (hr : rU.val = rn)
    (hposs : rn = 0 ∨ rn = 128) :
    (Contracts.bitOr rU (shl 6 (boolToWord true))).val = rn + 64 := by
  rcases hposs with rfl | rfl <;>
    simp [boolToWord, Contracts.bitOr, Verity.Core.Uint256.or, shl,
      Verity.Core.Uint256.shl, Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq, hr] <;>
    native_decide

private theorem bitOr_shl_5_true_val
    (rU : Uint256) {rn : Nat} (hr : rU.val = rn)
    (hposs : rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192) :
    (Contracts.bitOr rU (shl 5 (boolToWord true))).val = rn + 32 := by
  rcases hposs with rfl | rfl | rfl | rfl <;>
    simp [boolToWord, Contracts.bitOr, Verity.Core.Uint256.or, shl,
      Verity.Core.Uint256.shl, Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq, hr] <;>
    native_decide

private theorem bitOr_shl_4_true_val
    (rU : Uint256) {rn : Nat} (hr : rU.val = rn)
    (hposs :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224) :
    (Contracts.bitOr rU (shl 4 (boolToWord true))).val = rn + 16 := by
  rcases hposs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boolToWord, Contracts.bitOr, Verity.Core.Uint256.or, shl,
      Verity.Core.Uint256.shl, Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq, hr] <;>
    native_decide

private theorem bitOr_shl_3_true_val
    (rU : Uint256) {rn : Nat} (hr : rU.val = rn)
    (hposs :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224 ∨
          rn = 16 ∨ rn = 144 ∨ rn = 80 ∨ rn = 208 ∨
            rn = 48 ∨ rn = 176 ∨ rn = 112 ∨ rn = 240) :
    (Contracts.bitOr rU (shl 3 (boolToWord true))).val = rn + 8 := by
  rcases hposs with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boolToWord, Contracts.bitOr, Verity.Core.Uint256.or, shl,
      Verity.Core.Uint256.shl, Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq, hr] <;>
    native_decide

private theorem bitOr_shl_false_val
    (rU bitShift : Uint256) {rn : Nat} (hr : rU.val = rn)
    (hposs :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224 ∨
          rn = 16 ∨ rn = 144 ∨ rn = 80 ∨ rn = 208 ∨
            rn = 48 ∨ rn = 176 ∨ rn = 112 ∨ rn = 240 ∨
              rn = 8 ∨ rn = 136 ∨ rn = 72 ∨ rn = 200 ∨
                rn = 40 ∨ rn = 168 ∨ rn = 104 ∨ rn = 232 ∨
                  rn = 24 ∨ rn = 152 ∨ rn = 88 ∨ rn = 216 ∨
                    rn = 56 ∨ rn = 184 ∨ rn = 120 ∨ rn = 248) :
    (Contracts.bitOr rU (shl bitShift (boolToWord false))).val = rn := by
  rcases hposs with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boolToWord, Contracts.bitOr, Verity.Core.Uint256.or, shl,
      Verity.Core.Uint256.shl, Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq, hr] <;>
    native_decide

private theorem clzScanUint_val (x : Uint256) :
    (clzScanUint x).val = clzScanNat x.val := by
  unfold clzScanUint clzScanNat
  let ru1 : Uint256 :=
    shl 7 (boolToWord (0xffffffffffffffffffffffffffffffff < x))
  let rn1 : Nat := clzScanStepNat x.val 0 128
  have hru1 : ru1.val = rn1 := by
    dsimp [ru1, rn1, clzScanStepNat]
    have hBranch :
        (0xffffffffffffffffffffffffffffffff < x) ↔
          2 ^ 128 - 1 < x.val / 2 ^ 0 := by
      change (0xffffffffffffffffffffffffffffffff : Uint256).val < x.val ↔
        2 ^ 128 - 1 < x.val / 2 ^ 0
      rw [clzThreshold128_val]
      norm_num
    by_cases h : 2 ^ 128 - 1 < x.val / 2 ^ 0
    · have hUint := hBranch.mpr h
      have hVal : (0xffffffffffffffffffffffffffffffff : Uint256).val < x.val := hUint
      have hCond : 340282366920938463463374607431768211455 < x.val := by
        simpa using hVal
      simp [hCond]
      native_decide
    · have hUint : ¬ 0xffffffffffffffffffffffffffffffff < x :=
        fun hh => h (hBranch.mp hh)
      have hVal : ¬ (0xffffffffffffffffffffffffffffffff : Uint256).val < x.val := hUint
      have hCond : ¬ 340282366920938463463374607431768211455 < x.val := by
        simpa using hVal
      simp [hCond]
      native_decide
  let ru2 : Uint256 :=
    Contracts.bitOr ru1 (shl 6 (boolToWord (0xffffffffffffffff < shr ru1 x)))
  let rn2 : Nat := clzScanStepNat x.val rn1 64
  have hrn1 : rn1 = 0 ∨ rn1 = 128 := by
    simpa [rn1] using clzScanStepNat_128_possible x.val
  have hru2 : ru2.val = rn2 := by
    dsimp [ru2, rn2]
    exact clzScanStepUint_val x ru1 6 0xffffffffffffffff rn1 64 hru1
      (by native_decide)
      (bitOr_shl_6_true_val ru1 hru1 hrn1)
      (bitOr_shl_false_val ru1 6 hru1 (by omega))
  let ru3 : Uint256 :=
    Contracts.bitOr ru2 (shl 5 (boolToWord (0xffffffff < shr ru2 x)))
  let rn3 : Nat := clzScanStepNat x.val rn2 32
  have hrn2 : rn2 = 0 ∨ rn2 = 128 ∨ rn2 = 64 ∨ rn2 = 192 := by
    simpa [rn2] using clzScanStepNat_64_possible x.val rn1 hrn1
  have hru3 : ru3.val = rn3 := by
    dsimp [ru3, rn3]
    exact clzScanStepUint_val x ru2 5 0xffffffff rn2 32 hru2
      (by native_decide)
      (bitOr_shl_5_true_val ru2 hru2 hrn2)
      (bitOr_shl_false_val ru2 5 hru2 (by omega))
  let ru4 : Uint256 :=
    Contracts.bitOr ru3 (shl 4 (boolToWord (0xffff < shr ru3 x)))
  let rn4 : Nat := clzScanStepNat x.val rn3 16
  have hrn3 :
      rn3 = 0 ∨ rn3 = 128 ∨ rn3 = 64 ∨ rn3 = 192 ∨
        rn3 = 32 ∨ rn3 = 160 ∨ rn3 = 96 ∨ rn3 = 224 := by
    simpa [rn3] using clzScanStepNat_32_possible x.val rn2 hrn2
  have hru4 : ru4.val = rn4 := by
    dsimp [ru4, rn4]
    exact clzScanStepUint_val x ru3 4 0xffff rn3 16 hru3
      (by native_decide)
      (bitOr_shl_4_true_val ru3 hru3 hrn3)
      (bitOr_shl_false_val ru3 4 hru3 (by omega))
  let ru5 : Uint256 :=
    Contracts.bitOr ru4 (shl 3 (boolToWord (0xff < shr ru4 x)))
  let rn5 : Nat := clzScanStepNat x.val rn4 8
  have hrn4 :
      rn4 = 0 ∨ rn4 = 128 ∨ rn4 = 64 ∨ rn4 = 192 ∨
        rn4 = 32 ∨ rn4 = 160 ∨ rn4 = 96 ∨ rn4 = 224 ∨
          rn4 = 16 ∨ rn4 = 144 ∨ rn4 = 80 ∨ rn4 = 208 ∨
            rn4 = 48 ∨ rn4 = 176 ∨ rn4 = 112 ∨ rn4 = 240 := by
    simpa [rn4] using clzScanStepNat_16_possible x.val rn3 hrn3
  have hru5 : ru5.val = rn5 := by
    dsimp [ru5, rn5]
    exact clzScanStepUint_val x ru4 3 0xff rn4 8 hru4
      (by native_decide)
      (bitOr_shl_3_true_val ru4 hru4 hrn4)
      (bitOr_shl_false_val ru4 3 hru4 (by omega))
  change ru5.val = rn5
  exact hru5

def deBruijnLookup (y : Uint256) : Uint256 :=
  Contracts.byte (Contracts.bitAnd 0x1f (shr y FixedPointMathLibBase.clzDeBruijnMagic))
    FixedPointMathLibBase.clzDeBruijnTable

theorem deBruijnLookup_val_fin (y : Fin 256) (hy : y.val ≠ 0) :
    (deBruijnLookup (y.val : Uint256)).val = 255 - Nat.log2 y.val := by
  fin_cases y <;> native_decide

theorem deBruijnLookup_val
    (y : Nat) (hy_pos : 0 < y) (hy_lt : y < 256) :
    (deBruijnLookup (y : Uint256)).val = 255 - Nat.log2 y := by
  simpa using deBruijnLookup_val_fin ⟨y, hy_lt⟩ (Nat.ne_of_gt hy_pos)

private theorem bitXor_val (a b : Uint256) :
    (Contracts.bitXor a b).val =
      Nat.xor a.val b.val % Verity.Core.Uint256.modulus := by
  simp [Contracts.bitXor, Verity.Core.Uint256.xor, Verity.Core.Uint256.ofNat]

private theorem add_val_of_lt (a b : Uint256)
    (h : a.val + b.val < Verity.Core.Uint256.modulus) :
    (add a b).val = a.val + b.val := by
  simpa [HAdd.hAdd] using
    Verity.Core.Uint256.add_eq_of_lt (a := a) (b := b) h

private theorem clzXor_eq
    (r n : Nat) (hrmod : r % 8 = 0) (hrle : r ≤ 248) (hn : n < 8) :
    Nat.xor r (255 - n) = 255 - (r + n) := by
  interval_cases r <;> simp at hrmod <;> interval_cases n <;> native_decide

def clzFormulaUint (x : Uint256) : Uint256 :=
  let r := clzScanUint x
  add (Contracts.bitXor r (deBruijnLookup (shr r x))) (boolToWord (x == 0))

theorem clz_run_eq_formula (x : Uint256) (s : ContractState) :
    ((FixedPointMathLibBase.clz x).run s).fst = clzFormulaUint x := by
  rw [FixedPointMathLibBase.clz.eq_1]
  simp [clzFormulaUint, clzScanUint, deBruijnLookup, Verity.pure, Pure.pure, Contract.run]

theorem clz_apply_eq_success (x : Uint256) (s : ContractState) :
    FixedPointMathLibBase.clz x s = ContractResult.success (clzFormulaUint x) s := by
  rw [FixedPointMathLibBase.clz.eq_1]
  simp [clzFormulaUint, clzScanUint, deBruijnLookup, Verity.pure, Pure.pure]

theorem clzFormulaUint_val (x : Uint256) :
    (clzFormulaUint x).val =
      if x.val = 0 then 256 else 255 - Nat.log2 x.val := by
  by_cases hx0 : x.val = 0
  · have hxEq : x = 0 := by
      apply Verity.Core.Uint256.ext
      simpa using hx0
    subst hxEq
    native_decide
  · have hxPos : 0 < x.val := Nat.pos_of_ne_zero hx0
    have hx256 : x.val < 2 ^ 256 := by
      simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
    let rU := clzScanUint x
    let r := clzScanNat x.val
    let y := x.val / 2 ^ r
    have hR : rU.val = r := by
      simpa [rU, r] using clzScanUint_val x
    have hYVal : (shr rU x).val = y := by
      simp [y, shr_val, hR]
    have hyPos : 0 < y := by
      simpa [y, r] using clzWindow_pos x.val hx0 hx256
    have hyLt : y < 256 := by
      simpa [y, r] using clzWindow_lt_256 x.val hx0 hx256
    have hYEq : shr rU x = (y : Uint256) := by
      apply Verity.Core.Uint256.ext
      rw [hYVal]
      simp [Verity.Core.Uint256.ofNat]
      exact (Nat.mod_eq_of_lt (lt_trans hyLt
        (by native_decide : 256 < Verity.Core.Uint256.modulus))).symm
    have hLookup :
        (deBruijnLookup (shr rU x)).val = 255 - Nat.log2 y := by
      have h := deBruijnLookup_val y hyPos hyLt
      simpa [hYEq] using h
    have hLogY : Nat.log2 y = Nat.log2 x.val - r := by
      simpa [y, r] using log2_clzWindow x.val hx0 hx256
    have hLogYLt : Nat.log2 y < 8 := (Nat.log2_lt (Nat.ne_of_gt hyPos)).2 hyLt
    have hRMod : r % 8 = 0 := by
      simpa [r] using clzScanNat_mod_eight x.val hx0 hx256
    have hRLe : r ≤ 248 := by
      simpa [r] using clzScanNat_le_248 x.val hx0 hx256
    have hRLeLog : r ≤ Nat.log2 x.val := by
      simpa [r] using clzScanNat_le_log2 x.val hx0 hx256
    have hXorRaw :
        Nat.xor r (255 - Nat.log2 y) = 255 - Nat.log2 x.val := by
      have hxor := clzXor_eq r (Nat.log2 y) hRMod hRLe hLogYLt
      have hsum : r + Nat.log2 y = Nat.log2 x.val := by
        rw [hLogY]
        omega
      simpa [hsum] using hxor
    have hXorVal :
        (Contracts.bitXor rU (deBruijnLookup (shr rU x))).val =
          255 - Nat.log2 x.val := by
      rw [bitXor_val, hR, hLookup]
      have hlt : Nat.xor r (255 - Nat.log2 y) < Verity.Core.Uint256.modulus := by
        rw [hXorRaw]
        exact lt_of_le_of_lt (Nat.sub_le 255 (Nat.log2 x.val))
          (by native_decide : 255 < Verity.Core.Uint256.modulus)
      rw [Nat.mod_eq_of_lt hlt, hXorRaw]
    have hxNeUint : x ≠ 0 := by
      intro h
      apply hx0
      simp [h]
    have hBool : (boolToWord (x == 0)).val = 0 := by
      simp [hxNeUint]
    have hAddLt :
        (Contracts.bitXor rU (deBruijnLookup (shr rU x))).val +
          (boolToWord (x == 0)).val < Verity.Core.Uint256.modulus := by
      rw [hXorVal, hBool]
      exact lt_of_le_of_lt (Nat.sub_le 255 (Nat.log2 x.val))
        (by native_decide : 255 < Verity.Core.Uint256.modulus)
    change
      (add (Contracts.bitXor rU (deBruijnLookup (shr rU x))) (boolToWord (x == 0))).val =
        if x.val = 0 then 256 else 255 - Nat.log2 x.val
    rw [add_val_of_lt _ _ hAddLt, hXorVal, hBool]
    simp [hx0]

theorem clz_run_val (x : Uint256) (s : ContractState) :
    ((FixedPointMathLibBase.clz x).run s).fst.val =
      if x.val = 0 then 256 else 255 - Nat.log2 x.val := by
  rw [clz_run_eq_formula x s]
  exact clzFormulaUint_val x

end Tamago.Proof.Utils.ClzProof
