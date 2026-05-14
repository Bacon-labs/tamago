import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Sqrt
import Cbrt.OverflowSafety
import Tamago.Proof.Utils.ClzProof
import Tamago.Spec.Utils.FixedPointMathLibSpec
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Utils.FixedPointMathLibProof

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 300

open Verity
open Verity.EVM.Uint256
open Tamago.Utils
open Tamago.Spec.Utils.FixedPointMathLibSpec
open Tamago.Utils.FixedPointMathLib
open Sqrt.Model
open Sqrt.FloorBound
open Sqrt.OctaveCert
open Sqrt.ErrorChain
open Sqrt.Wiring
open Sqrt.Correctness
open Cbrt.Model
open Cbrt.FloorBound
open Cbrt.Contraction
open Cbrt.OctaveCert
open Cbrt.ErrorChain
open Cbrt.Wiring
open Cbrt.Correctness
open Cbrt.OverflowSafety

attribute [local simp] maxUint256 saturatingAdd saturatingMul saturatingSub
  Tamago.Utils.FixedPointMathLib.dist sqrt clamp
attribute [local simp] Tamago.Utils.FixedPointMathLibBase.maxUint256
  Tamago.Utils.FixedPointMathLibBase.saturatingAdd
  Tamago.Utils.FixedPointMathLibBase.saturatingMul
  Tamago.Utils.FixedPointMathLibBase.saturatingSub
  Tamago.Utils.FixedPointMathLibBase.dist
  Tamago.Utils.FixedPointMathLibBase.avg
  Tamago.Utils.FixedPointMathLibBase.sqrt
  Tamago.Utils.FixedPointMathLibBase.clamp
attribute [local simp] Contracts.min Contracts.max

private theorem bind_pure_contract {α β : Type} (a : α) (f : α → Contract β) :
    Verity.bind (Verity.pure a) f = f a := by
  funext s
  simp [Verity.bind, Verity.pure]

private def saturatingAdd_property (x y result : Uint256) : Prop :=
  (x.val + y.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    result.val = x.val + y.val) ∧
  (Verity.Stdlib.Math.MAX_UINT256 < x.val + y.val →
    result = maxUint256) ∧
  x.val ≤ result.val ∧
  y.val ≤ result.val

private def saturatingSub_property (x y result : Uint256) : Prop :=
  (x.val ≤ y.val → result = 0) ∧
  (y.val ≤ x.val → result.val + y.val = x.val) ∧
  result.val ≤ x.val

private def saturatingMul_property (x y result : Uint256) : Prop :=
  (x.val * y.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    result.val = x.val * y.val) ∧
  (Verity.Stdlib.Math.MAX_UINT256 < x.val * y.val →
    result = maxUint256) ∧
  (x.val = 0 ∨ y.val = 0 → result = 0)

private def dist_property (x y result : Uint256) : Prop :=
  (x.val ≤ y.val → result.val + x.val = y.val) ∧
  (y.val ≤ x.val → result.val + y.val = x.val)

private def avg_property (x y result : Uint256) : Prop :=
  2 * result.val ≤ x.val + y.val ∧
  x.val + y.val < 2 * (result.val + 1)

private def sqrt_property (x result : Uint256) : Prop :=
  result.val * result.val ≤ x.val ∧
  x.val < (result.val + 1) * (result.val + 1)

private def cbrt_property (x result : Uint256) : Prop :=
  result.val * result.val * result.val ≤ x.val ∧
  x.val < (result.val + 1) * (result.val + 1) * (result.val + 1)

private def logFloor_property (base : Nat) (x result : Uint256) : Prop :=
  (x.val = 0 → result = 0) ∧
  (x.val ≠ 0 → base ^ result.val ≤ x.val) ∧
  x.val < base ^ (result.val + 1)

private def logUp_property (base : Nat) (x result : Uint256) : Prop :=
  (x.val = 0 → result = 0) ∧
  x.val ≤ base ^ result.val ∧
  (1 < x.val → base ^ (result.val - 1) < x.val)

private def clamp_property (x minValue maxValue result : Uint256) : Prop :=
  (maxValue.val < minValue.val → result = maxValue) ∧
  (minValue.val ≤ maxValue.val →
    minValue.val ≤ result.val ∧ result.val ≤ maxValue.val) ∧
  (minValue.val ≤ x.val ∧ x.val ≤ maxValue.val → result = x) ∧
  (x.val < minValue.val ∧ minValue.val ≤ maxValue.val → result = minValue) ∧
  (maxValue.val < x.val → result = maxValue)

private theorem maxUint256_val :
    (maxUint256 : Uint256).val = Verity.Stdlib.Math.MAX_UINT256 := by
  simp [maxUint256, Tamago.Utils.FixedPointMathLibBase.maxUint256,
    Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256, HSub.hSub,
    Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

private theorem room_val (x : Uint256) :
    (sub maxUint256 x).val = Verity.Stdlib.Math.MAX_UINT256 - x.val := by
  have hX : x.val ≤ (maxUint256 : Uint256).val := by
    rw [maxUint256_val]
    exact Verity.Core.Uint256.val_le_max x
  simpa [HSub.hSub, maxUint256_val]
    using Verity.Core.Uint256.sub_eq_of_le (a := maxUint256) (b := x) hX

private theorem maxUint256_lt_modulus :
    Verity.Stdlib.Math.MAX_UINT256 < Verity.Core.Uint256.modulus := by
  have hSucc :
      Verity.Stdlib.Math.MAX_UINT256 + 1 = Verity.Core.Uint256.modulus := by
    simpa [Verity.Stdlib.Math.MAX_UINT256]
      using Verity.Core.Uint256.max_uint256_succ_eq_modulus
  rw [← hSucc]
  exact Nat.lt_succ_self _

private theorem div_maxUint256_val (x : Uint256) (hx : x.val ≠ 0) :
    (div maxUint256 x).val = Verity.Stdlib.Math.MAX_UINT256 / x.val := by
  have hDivLt :
      Verity.Stdlib.Math.MAX_UINT256 / x.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) maxUint256_lt_modulus
  simp [HDiv.hDiv, div, Verity.Core.Uint256.div, hx, Verity.Core.Uint256.ofNat]
  have hRaw : (sub 0 1 : Uint256).val = Verity.Stdlib.Math.MAX_UINT256 := by
    simpa [maxUint256, Tamago.Utils.FixedPointMathLibBase.maxUint256] using maxUint256_val
  rw [hRaw]
  exact Nat.mod_eq_of_lt hDivLt

private theorem div_two_val (x : Uint256) :
    (div x 2).val = x.val / 2 := by
  have hDivLt : x.val / 2 < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  simp [HDiv.hDiv, div, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt hDivLt

private theorem div_val (a b : Uint256) (hb : b.val ≠ 0) :
    (div a b).val = a.val / b.val := by
  have hLt : a.val / b.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
  simp [HDiv.hDiv, div, Verity.Core.Uint256.div, hb, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt hLt

private theorem shr_val (shift value : Uint256) :
    (shr shift value).val = value.val / 2 ^ shift.val := by
  have hLt : value.val / 2 ^ shift.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) value.isLt
  simp [shr, Verity.Core.Uint256.shr, Verity.Core.Uint256.ofNat,
    Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt hLt

private theorem shl_val (shift value : Uint256) :
    (shl shift value).val =
      (value.val * 2 ^ shift.val) % Verity.Core.Uint256.modulus := by
  simp [shl, Verity.Core.Uint256.shl, Verity.Core.Uint256.ofNat,
    Nat.shiftLeft_eq]

private theorem shl_zero_of_shift_ge_256 (shift value : Uint256)
    (h : 256 ≤ shift.val) :
    (shl shift value).val = 0 := by
  rw [shl_val]
  have hshift : shift.val = 256 + (shift.val - 256) := by omega
  rw [hshift, Nat.pow_add]
  change value.val * (2 ^ 256 * 2 ^ (shift.val - 256)) % 2 ^ 256 = 0
  rw [← Nat.mul_assoc]
  rw [Nat.mul_comm value.val (2 ^ 256)]
  rw [Nat.mul_assoc]
  exact Nat.mul_mod_right _ _

private def uintOfNat (n : Nat) : Uint256 :=
  Verity.Core.Uint256.ofNat n

private theorem uintOfNat_val_of_lt {n : Nat}
    (h : n < Verity.Core.Uint256.modulus) :
    (uintOfNat n).val = n := by
  simp [uintOfNat, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem add_small_val (a : Uint256) {b : Nat}
    (h : a.val + b < Verity.Core.Uint256.modulus) :
    (add a (uintOfNat b)).val = a.val + b := by
  have hbLt : b < Verity.Core.Uint256.modulus := by omega
  have hAddLt :
      a.val + (uintOfNat b).val < Verity.Core.Uint256.modulus := by
    rw [uintOfNat_val_of_lt hbLt]
    exact h
  simpa [HAdd.hAdd, uintOfNat_val_of_lt hbLt] using
    Verity.Core.Uint256.add_eq_of_lt (a := a) (b := uintOfNat b) hAddLt

private theorem mul_small_val (a : Uint256) {b : Nat}
    (hbLt : b < Verity.Core.Uint256.modulus)
    (h : a.val * b < Verity.Core.Uint256.modulus) :
    (mul a (uintOfNat b)).val = a.val * b := by
  have hMulLt :
      a.val * (uintOfNat b).val < Verity.Core.Uint256.modulus := by
    rw [uintOfNat_val_of_lt hbLt]
    exact h
  simpa [HMul.hMul, uintOfNat_val_of_lt hbLt] using
    Verity.Core.Uint256.mul_eq_of_lt (a := a) (b := uintOfNat b) hMulLt

private theorem add_val_of_lt (a b : Uint256)
    (h : a.val + b.val < Verity.Core.Uint256.modulus) :
    (add a b).val = a.val + b.val := by
  simpa [HAdd.hAdd] using Verity.Core.Uint256.add_eq_of_lt (a := a) (b := b) h

private theorem sub_small_val (a : Uint256) {b : Nat}
    (h : b ≤ a.val) :
    (sub a (uintOfNat b)).val = a.val - b := by
  have hbLt : b < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt h a.isLt
  have hLe : (uintOfNat b).val ≤ a.val := by
    rw [uintOfNat_val_of_lt hbLt]
    exact h
  simpa [HSub.hSub, uintOfNat_val_of_lt hbLt] using
    Verity.Core.Uint256.sub_eq_of_le (a := a) (b := uintOfNat b) hLe

private theorem sub_zero_val (a : Uint256) :
    (sub a 0).val = a.val := by
  have hLe : (0 : Uint256).val ≤ a.val := by simp
  simpa [HSub.hSub] using
    Verity.Core.Uint256.sub_eq_of_le (a := a) (b := (0 : Uint256)) hLe

private theorem sub_boolToWord_val_eq_if (z : Uint256) (p : Prop) [Decidable p] :
    (sub z (boolToWord p)).val = (if p then sub z 1 else z).val := by
  by_cases hp : p
  · simp [hp, boolToWord]
  · simp [hp, boolToWord, sub_zero_val]

private theorem bitOr_val (a b : Uint256) :
    (Contracts.bitOr a b).val =
      Nat.lor a.val b.val % Verity.Core.Uint256.modulus := by
  simp [Contracts.bitOr, Verity.Core.Uint256.or, Verity.Core.Uint256.ofNat]

private theorem bitOr_val_of_lt (a b : Uint256)
    (h : Nat.lor a.val b.val < Verity.Core.Uint256.modulus) :
    (Contracts.bitOr a b).val = Nat.lor a.val b.val := by
  rw [bitOr_val]
  exact Nat.mod_eq_of_lt h

private theorem bitXor_val (a b : Uint256) :
    (Contracts.bitXor a b).val =
      Nat.xor a.val b.val % Verity.Core.Uint256.modulus := by
  simp [Contracts.bitXor, Verity.Core.Uint256.xor, Verity.Core.Uint256.ofNat]

private theorem bitXor_val_of_lt (a b : Uint256)
    (h : Nat.xor a.val b.val < Verity.Core.Uint256.modulus) :
    (Contracts.bitXor a b).val = Nat.xor a.val b.val := by
  rw [bitXor_val]
  exact Nat.mod_eq_of_lt h

private theorem mod_val (a b : Uint256) (hb : b.val ≠ 0) :
    (mod a b).val = a.val % b.val := by
  have hLt : a.val % b.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hb))
      (Nat.le_of_lt b.isLt)
  simp [HMod.hMod, mod, Verity.Core.Uint256.mod, hb, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt hLt

private theorem byte_val (index value : Uint256) :
    (byte index value).val =
      if index.val > 31 then 0 else (value.val / 2 ^ ((31 - index.val) * 8)) % 256 := by
  by_cases h : 31 < index.val
  · simp [Verity.Core.Uint256.byte, Verity.Core.Uint256.ofNat, h]
  · simp [Verity.Core.Uint256.byte, Verity.Core.Uint256.ofNat, Nat.shiftRight_eq_div_pow,
      h, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    rw [Nat.and_two_pow_sub_one_eq_mod
      (x := value.val / 2 ^ ((31 - index.val) * 8)) (n := 8)]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 256))
      (by native_decide : 256 < 2 ^ 256))

private theorem cbrtPackedMultiplierByte_val (bU : Uint256) (b : Nat)
    (hbVal : bU.val = b) :
    (byte (add 29 (mod bU 3)) 0x90b5e5).val = cbrtSeedMultiplier b := by
  have hThree : (3 : Uint256).val = 3 := by native_decide
  have hModVal : (mod bU 3).val = b % 3 := by
    rw [mod_val bU 3 (by rw [hThree]; norm_num), hbVal, hThree]
  have hModLt : b % 3 < 3 := Nat.mod_lt _ (by decide)
  have hIndexLt : (29 : Uint256).val + (mod bU 3).val < Verity.Core.Uint256.modulus := by
    have h29 : (29 : Uint256).val = 29 := by native_decide
    have hBound : 32 < Verity.Core.Uint256.modulus := by native_decide
    rw [h29, hModVal]
    omega
  have hIndexVal : (add 29 (mod bU 3)).val = 29 + b % 3 := by
    have h := add_val_of_lt (29 : Uint256) (mod bU 3) hIndexLt
    simpa [hModVal] using h
  rw [byte_val, hIndexVal]
  have hIndexLe : ¬ 31 < 29 + b % 3 := by omega
  simp [hIndexLe, cbrtSeedMultiplier]
  have hCases : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hCases with h | h | h <;> simp [h] <;> native_decide

@[simp] private theorem uintOne_val : (1 : Uint256).val = 1 := by
  native_decide

@[simp] private theorem uintTwoFiveSix_val : (256 : Uint256).val = 256 := by
  native_decide

private theorem sqrtExponentUint_val (x : Uint256) :
    (shr 1 (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x))).val =
      if x.val = 0 then 0 else (Nat.log2 x.val + 1) / 2 := by
  rw [shr_val]
  by_cases hx0 : x.val = 0
  · have hClz :
        (Tamago.Proof.Utils.ClzProof.clzFormulaUint x).val = 256 := by
      simp [Tamago.Proof.Utils.ClzProof.clzFormulaUint_val, hx0]
    have hLe :
        (Tamago.Proof.Utils.ClzProof.clzFormulaUint x).val ≤ (256 : Uint256).val := by
      simp [hClz]
    have hSub :
        (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x)).val = 0 := by
      have h := Verity.Core.Uint256.sub_eq_of_le
        (a := (256 : Uint256))
        (b := Tamago.Proof.Utils.ClzProof.clzFormulaUint x) hLe
      simpa [HSub.hSub, hClz] using h
    simp [hx0, hSub]
  · have hxPos : 0 < x.val := Nat.pos_of_ne_zero hx0
    have hxLt : x.val < 2 ^ 256 := by
      simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
    have hLogLt : Nat.log2 x.val < 256 :=
      (Nat.log2_lt (Nat.ne_of_gt hxPos)).2 hxLt
    have hClz :
        (Tamago.Proof.Utils.ClzProof.clzFormulaUint x).val =
          255 - Nat.log2 x.val := by
      simp [Tamago.Proof.Utils.ClzProof.clzFormulaUint_val, hx0]
    have hLe :
        (Tamago.Proof.Utils.ClzProof.clzFormulaUint x).val ≤ (256 : Uint256).val := by
      rw [hClz, uintTwoFiveSix_val]
      omega
    have hSub :
        (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x)).val =
          Nat.log2 x.val + 1 := by
      have h := Verity.Core.Uint256.sub_eq_of_le
        (a := (256 : Uint256))
        (b := Tamago.Proof.Utils.ClzProof.clzFormulaUint x) hLe
      have hRaw :
          (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x)).val =
            256 - (255 - Nat.log2 x.val) := by
        simpa [HSub.hSub, hClz] using h
      rw [hRaw]
      omega
    simp [hx0, hSub]

private theorem sqrtSeedUint_val_of_ne (x : Uint256) (hx0 : x.val ≠ 0) :
    (shl (shr 1 (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x))) 1).val =
      sqrtSeed x.val := by
  have hQ := sqrtExponentUint_val x
  rw [if_neg hx0] at hQ
  rw [shl_val, hQ]
  have hxPos : 0 < x.val := Nat.pos_of_ne_zero hx0
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hLogLt : Nat.log2 x.val < 256 :=
    (Nat.log2_lt (Nat.ne_of_gt hxPos)).2 hxLt
  have hShiftLt : (Nat.log2 x.val + 1) / 2 < 256 := by
    omega
  have hPowLt :
      1 * 2 ^ ((Nat.log2 x.val + 1) / 2) < Verity.Core.Uint256.modulus := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using
      Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hShiftLt
  rw [uintOne_val]
  rw [Nat.mod_eq_of_lt hPowLt]
  unfold sqrtSeed
  simp [hx0, Nat.shiftLeft_eq]

private theorem sqrt_m_lt_pow128_of_u256
    (m x : Nat)
    (hmlo : m * m ≤ x)
    (hx : x < Verity.Core.Uint256.modulus) :
    m < 2 ^ 128 := by
  by_cases hm128 : m < 2 ^ 128
  · exact hm128
  · have hmGe : 2 ^ 128 ≤ m := Nat.le_of_not_lt hm128
    have hmSqGe : 2 ^ 256 ≤ m * m := by
      have hpow : 2 ^ 256 = (2 ^ 128) * (2 ^ 128) := by
        calc
          2 ^ 256 = 2 ^ (128 + 128) := by decide
          _ = (2 ^ 128) * (2 ^ 128) := by rw [Nat.pow_add]
      have hmul : (2 ^ 128) * (2 ^ 128) ≤ m * m := Nat.mul_le_mul hmGe hmGe
      simpa [hpow] using hmul
    have hxGe : 2 ^ 256 ≤ x := Nat.le_trans hmSqGe hmlo
    exact False.elim ((Nat.not_lt_of_ge hxGe)
      (by simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using hx))

private theorem sqrt_x_div_m_le_m_plus_two
    (x m : Nat)
    (hm : 0 < m)
    (hmhi : x < (m + 1) * (m + 1)) :
    x / m ≤ m + 2 := by
  have hmhi' : x < m * m + 2 * m + 1 := by
    have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    simpa [hsq] using hmhi
  have hmhi'' : x < (m * m + 2 * m) + 1 := by omega
  have hxLe : x ≤ m * m + 2 * m := Nat.lt_succ_iff.mp hmhi''
  calc
    x / m ≤ (m * m + 2 * m) / m := Nat.div_le_div_right hxLe
    _ = (m + 2) * m / m := by rw [Nat.add_mul]
    _ = m + 2 := Nat.mul_div_cancel (m + 2) hm

private theorem sqrt_sum_lt_uint256_of_cert
    (x m z d : Nat)
    (hx : x < Verity.Core.Uint256.modulus)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hmz : m ≤ z)
    (hzd : z - m ≤ d)
    (hdm : d ≤ m) :
    z + x / z < Verity.Core.Uint256.modulus := by
  have hdiv_z_m : x / z ≤ x / m := Nat.div_le_div_left hmz hm
  have hdiv_m : x / m ≤ m + 2 := sqrt_x_div_m_le_m_plus_two x m hm hmhi
  have hdiv : x / z ≤ m + 2 := Nat.le_trans hdiv_z_m hdiv_m
  have hz_le_md : z ≤ d + m := (Nat.sub_le_iff_le_add).1 hzd
  have hz_le_2m : z ≤ 2 * m := by omega
  have hsum_lt_const : z + x / z < 3 * (2 ^ 128) + 2 := by
    have hm128 : m < 2 ^ 128 := sqrt_m_lt_pow128_of_u256 m x hmlo hx
    omega
  have hconst : 3 * (2 ^ 128) + 2 < Verity.Core.Uint256.modulus := by
    native_decide
  exact Nat.lt_trans hsum_lt_const hconst

private theorem sqrtSeed_sum_lt_uint256
    (i : Fin 256) (x : Nat)
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    Sqrt.OctaveCert.seedOf i + x / Sqrt.OctaveCert.seedOf i < Verity.Core.Uint256.modulus := by
  have hsPos : 0 < Sqrt.OctaveCert.seedOf i := by
    simp [Sqrt.OctaveCert.seedOf, Nat.shiftLeft_eq]
  have hk_le : (i.val + 1) / 2 ≤ 128 := by omega
  have hz_le : Sqrt.OctaveCert.seedOf i ≤ 2 ^ 128 := by
    unfold Sqrt.OctaveCert.seedOf
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide : (2 : Nat) > 0) hk_le
  have hExp : i.val + 1 ≤ 2 * ((i.val + 1) / 2) + 1 := by omega
  have hPowLe : 2 ^ (i.val + 1) ≤ 2 ^ (2 * ((i.val + 1) / 2) + 1) :=
    Nat.pow_le_pow_right (by decide : (2 : Nat) > 0) hExp
  have hPowMul :
      2 ^ (2 * ((i.val + 1) / 2) + 1) =
        2 * Sqrt.OctaveCert.seedOf i * Sqrt.OctaveCert.seedOf i := by
    calc
      2 ^ (2 * ((i.val + 1) / 2) + 1) =
          2 ^ (2 * ((i.val + 1) / 2)) * 2 := by rw [Nat.pow_add]
      _ = (2 ^ ((i.val + 1) / 2) * 2 ^ ((i.val + 1) / 2)) * 2 := by
            rw [show 2 * ((i.val + 1) / 2) =
              ((i.val + 1) / 2) + ((i.val + 1) / 2) by omega, Nat.pow_add]
      _ = 2 * Sqrt.OctaveCert.seedOf i * Sqrt.OctaveCert.seedOf i := by
            unfold Sqrt.OctaveCert.seedOf
            simp [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_left_comm]
  have hxmul : x < 2 * Sqrt.OctaveCert.seedOf i * Sqrt.OctaveCert.seedOf i :=
    Nat.lt_of_lt_of_le hOct.2 (by simpa [hPowMul] using hPowLe)
  have hdiv : x / Sqrt.OctaveCert.seedOf i < 2 * Sqrt.OctaveCert.seedOf i := by
    exact (Nat.div_lt_iff_lt_mul hsPos).2
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hxmul)
  have hsum_lt :
      Sqrt.OctaveCert.seedOf i + x / Sqrt.OctaveCert.seedOf i <
        Sqrt.OctaveCert.seedOf i + 2 * Sqrt.OctaveCert.seedOf i := by omega
  have hsum_le : Sqrt.OctaveCert.seedOf i + 2 * Sqrt.OctaveCert.seedOf i ≤ 3 * (2 ^ 128) := by
    omega
  have hconst : 3 * (2 ^ 128) < Verity.Core.Uint256.modulus := by
    native_decide
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsum_lt hsum_le) (Nat.le_of_lt hconst)

private theorem sqrtFirstStepUint_val (x : Uint256) (hx0 : x.val ≠ 0) :
    (let q := shr 1 (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x))
     shr 1 (add (shl q 1) (shr q x))).val =
      sqrtStep x.val (sqrtSeed x.val) := by
  let q := shr 1 (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x))
  have hQ : q.val = (Nat.log2 x.val + 1) / 2 := by
    simpa [q, hx0] using sqrtExponentUint_val x
  have hSeedVal : (shl q 1).val = sqrtSeed x.val := by
    simpa [q] using sqrtSeedUint_val_of_ne x hx0
  have hShrVal : (shr q x).val = x.val / sqrtSeed x.val := by
    rw [shr_val, hQ]
    unfold sqrtSeed
    simp [hx0, Nat.shiftLeft_eq]
  have hxPos : 0 < x.val := Nat.pos_of_ne_zero hx0
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  let i : Fin 256 := ⟨Nat.log2 x.val, (Nat.log2_lt (Nat.ne_of_gt hxPos)).2 hxLt⟩
  have hOct : 2 ^ i.val ≤ x.val ∧ x.val < 2 ^ (i.val + 1) := by
    have hlog : 2 ^ Nat.log2 x.val ≤ x.val ∧ x.val < 2 ^ (Nat.log2 x.val + 1) := by
      constructor
      · simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.ne_of_gt hxPos)
      · simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self (by decide : 1 < 2) x.val
    simpa [i] using hlog
  have hSeedEq : sqrtSeed x.val = Sqrt.OctaveCert.seedOf i :=
    sqrtSeed_eq_octaveSeed i x.val hOct
  have hAddLt :
      (shl q 1).val + (shr q x).val < Verity.Core.Uint256.modulus := by
    rw [hSeedVal, hShrVal, hSeedEq]
    exact sqrtSeed_sum_lt_uint256 i x.val hOct
  have hAddVal :
      (add (shl q 1) (shr q x)).val = sqrtSeed x.val + x.val / sqrtSeed x.val := by
    rw [add_val_of_lt _ _ hAddLt, hSeedVal, hShrVal]
  change (shr 1 (add (shl q 1) (shr q x))).val = sqrtStep x.val (sqrtSeed x.val)
  rw [shr_val, hAddVal]
  simp [sqrtStep]

private theorem if_pure_run_fst {α : Type} [Inhabited α] (c : Prop) [Decidable c]
    (a b : α) (s : ContractState) :
    ((if c then Verity.pure a else Verity.pure b).run s).fst =
      if c then a else b := by
  by_cases h : c
  · simp [h, Contract.run, Verity.pure]
  · simp [h, Contract.run, Verity.pure]

private theorem contract_run_fst {α : Type} [Inhabited α]
    (c : Contract α) (s : ContractState) :
    (c.run s).fst = (c s).fst := by
  cases h : c s <;> simp [Contract.run, ContractResult.fst, h]

private theorem bind_success_run_fst {α β : Type} [Inhabited β]
    (ma : Contract α) (f : α → Contract β) (a : α) (s s' : ContractState)
    (h : ma s = ContractResult.success a s') :
    ((Verity.bind ma f).run s).fst = ((f a).run s').fst := by
  cases hfa : f a s' <;> simp [Contract.run, Verity.bind, h, hfa, ContractResult.fst]

private theorem monad_bind_success_run_fst {α β : Type} [Inhabited β]
    (ma : Contract α) (f : α → Contract β) (a : α) (s s' : ContractState)
    (h : ma s = ContractResult.success a s') :
    (((ma >>= f).run s).fst) = ((f a).run s').fst := by
  cases hfa : f a s' <;>
    simp [Contract.run, Bind.bind, Verity.bind, h, hfa, ContractResult.fst]

private theorem two_mul_div_two_le (n : Nat) :
    2 * (n / 2) ≤ n := by
  simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2

private theorem lt_two_mul_div_two_succ (n : Nat) :
    n < 2 * (n / 2 + 1) := by
  have hModLt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
  have hDecomp : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  omega

theorem saturatingAdd_saturates_at_uint256_max (x y : Uint256) (s : ContractState) :
    saturatingAdd_property x y ((saturatingAdd x y).run s).fst := by
  unfold saturatingAdd_property
  by_cases hOverflow : Verity.Stdlib.Math.MAX_UINT256 < x.val + y.val
  · have hBranch : y.val > (sub maxUint256 x).val := by
      rw [room_val]
      have hXMax : x.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [Verity.Stdlib.Math.MAX_UINT256] using Verity.Core.Uint256.val_le_max x
      omega
    have hBranchRaw : (sub (sub 0 1) x).val < y.val := by
      simpa [maxUint256, Tamago.Utils.FixedPointMathLibBase.maxUint256] using hBranch
    have hNotNoOverflow : ¬ x.val + y.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact False.elim (hNotNoOverflow h)
    · intro _h
      simp [saturatingAdd, Contract.run, Verity.pure, Pure.pure, hBranchRaw]
    · simp [saturatingAdd, Contract.run, Verity.pure, Pure.pure, hBranchRaw]
      simpa [Verity.Stdlib.Math.MAX_UINT256] using Verity.Core.Uint256.val_le_max x
    · simp [saturatingAdd, Contract.run, Verity.pure, Pure.pure, hBranchRaw]
      simpa [Verity.Stdlib.Math.MAX_UINT256] using Verity.Core.Uint256.val_le_max y
  · have hNoOverflow : x.val + y.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      omega
    have hNotBranch : ¬ y.val > (sub maxUint256 x).val := by
      rw [room_val]
      have hXMax : x.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [Verity.Stdlib.Math.MAX_UINT256] using Verity.Core.Uint256.val_le_max x
      omega
    have hNotBranchRaw : ¬ (sub (sub 0 1) x).val < y.val := by
      simpa [maxUint256, Tamago.Utils.FixedPointMathLibBase.maxUint256] using hNotBranch
    have hAddLt :
        x.val + y.val < Verity.Core.Uint256.modulus := by
      have hSucc :
          Verity.Stdlib.Math.MAX_UINT256 + 1 = Verity.Core.Uint256.modulus := by
        simpa [Verity.Stdlib.Math.MAX_UINT256]
          using Verity.Core.Uint256.max_uint256_succ_eq_modulus
      rw [← hSucc]
      exact Nat.lt_succ_of_le hNoOverflow
    have hAddVal : (add x y).val = x.val + y.val := by
      simpa [HAdd.hAdd] using Verity.Core.Uint256.add_eq_of_lt (a := x) (b := y) hAddLt
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _h
      simp [saturatingAdd, Contract.run, Verity.pure, Pure.pure, hNotBranchRaw, hAddVal]
    · intro h
      exact False.elim (hOverflow h)
    · simp [saturatingAdd, Contract.run, Verity.pure, Pure.pure, hNotBranchRaw, hAddVal]
    · simp [saturatingAdd, Contract.run, Verity.pure, Pure.pure, hNotBranchRaw, hAddVal]

theorem saturatingMul_saturates_at_uint256_max (x y : Uint256) (s : ContractState) :
    saturatingMul_property x y ((saturatingMul x y).run s).fst := by
  unfold saturatingMul_property
  by_cases hXZero : x = 0
  · have hxVal : x.val = 0 := by
      simp [hXZero]
    refine ⟨?_, ?_, ?_⟩
    · intro _h
      simp [saturatingMul, Contract.run, Verity.pure, Pure.pure, hXZero, mul, Verity.Core.Uint256.mul,
        Verity.Core.Uint256.ofNat]
    · intro hOverflow
      have hProdZero : x.val * y.val = 0 := by
        simp [hxVal]
      omega
    · intro _h
      apply Verity.Core.Uint256.ext
      simp [saturatingMul, Contract.run, Verity.pure, Pure.pure, hXZero, mul, Verity.Core.Uint256.mul,
        Verity.Core.Uint256.ofNat]
  · have hxValNe : x.val ≠ 0 := by
      intro hxVal
      apply hXZero
      exact Verity.Core.Uint256.ext (by simpa using hxVal)
    have hxPos : 0 < x.val := Nat.pos_of_ne_zero hxValNe
    have hLimit :
        (div maxUint256 x).val = Verity.Stdlib.Math.MAX_UINT256 / x.val :=
      div_maxUint256_val x hxValNe
    by_cases hOverflow : Verity.Stdlib.Math.MAX_UINT256 < x.val * y.val
    · have hBranch : (div maxUint256 x).val < y.val := by
        rw [hLimit]
        refine (Nat.div_lt_iff_lt_mul hxPos).2 ?_
        simpa [Nat.mul_comm] using hOverflow
      have hBranchRaw : (div (sub 0 1) x).val < y.val := by
        simpa [maxUint256, Tamago.Utils.FixedPointMathLibBase.maxUint256] using hBranch
      refine ⟨?_, ?_, ?_⟩
      · intro hNoOverflow
        omega
      · intro _h
        simp [saturatingMul, Contract.run, Verity.pure, Pure.pure, hXZero, hBranchRaw]
      · intro hZero
        rcases hZero with hx | hy
        · exact False.elim (hxValNe hx)
        · have hProdZero : x.val * y.val = 0 := by
            simp [hy]
          omega
    · have hNoOverflow : x.val * y.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        omega
      have hNotBranch : ¬ (div maxUint256 x).val < y.val := by
        rw [hLimit]
        have hyLe : y.val ≤ Verity.Stdlib.Math.MAX_UINT256 / x.val := by
          refine (Nat.le_div_iff_mul_le hxPos).2 ?_
          simpa [Nat.mul_comm] using hNoOverflow
        exact Nat.not_lt_of_ge hyLe
      have hNotBranchRaw : ¬ (div (sub 0 1) x).val < y.val := by
        simpa [maxUint256, Tamago.Utils.FixedPointMathLibBase.maxUint256] using hNotBranch
      have hMulLt :
          x.val * y.val < Verity.Core.Uint256.modulus := by
        have hSucc :
            Verity.Stdlib.Math.MAX_UINT256 + 1 = Verity.Core.Uint256.modulus := by
          simpa [Verity.Stdlib.Math.MAX_UINT256]
            using Verity.Core.Uint256.max_uint256_succ_eq_modulus
        rw [← hSucc]
        exact Nat.lt_succ_of_le hNoOverflow
      have hMulVal : (mul x y).val = x.val * y.val := by
        simpa [HMul.hMul] using
          Verity.Core.Uint256.mul_eq_of_lt (a := x) (b := y) hMulLt
      refine ⟨?_, ?_, ?_⟩
      · intro _h
        simp [saturatingMul, Contract.run, Verity.pure, Pure.pure, hNotBranchRaw, hMulVal]
      · intro h
        exact False.elim (hOverflow h)
      · intro hZero
        apply Verity.Core.Uint256.ext
        simp [saturatingMul, Contract.run, Verity.pure, Pure.pure, hNotBranchRaw, hMulVal]
        rcases hZero with hx | hy
        · exact False.elim (hxValNe hx)
        · simp [hy]

theorem saturatingSub_never_underflows (x y : Uint256) (s : ContractState) :
    saturatingSub_property x y ((saturatingSub x y).run s).fst := by
  unfold saturatingSub_property
  by_cases hUnderflow : y.val > x.val
  · have hNotLe : ¬ y.val ≤ x.val := by omega
    have hBranch : y > x := hUnderflow
    refine ⟨?_, ?_, ?_⟩
    · intro _h
      simp [saturatingSub, Contract.run, Verity.pure, Pure.pure, hBranch]
    · intro h
      exact False.elim (hNotLe h)
    · simp [saturatingSub, Contract.run, Verity.pure, Pure.pure, hBranch]
  · have hLe : y.val ≤ x.val := by omega
    have hNotBranch : ¬ y > x := by
      exact Nat.not_lt_of_ge hLe
    have hSubVal : (sub x y).val = x.val - y.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := x) (b := y) hLe
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hEq : x.val = y.val := by omega
      apply Verity.Core.Uint256.ext
      simp [saturatingSub, Contract.run, Verity.pure, Pure.pure, hNotBranch, hSubVal, hEq]
    · intro _h
      simp [saturatingSub, Contract.run, Verity.pure, Pure.pure, hNotBranch, hSubVal]
      omega
    · simp [saturatingSub, Contract.run, Verity.pure, Pure.pure, hNotBranch, hSubVal]

theorem dist_is_absolute_difference (x y : Uint256) (s : ContractState) :
    dist_property x y ((Tamago.Utils.FixedPointMathLib.dist x y).run s).fst := by
  unfold dist_property
  by_cases hGe : y.val ≤ x.val
  · have hBranch : x >= y := hGe
    have hSubVal : (sub x y).val = x.val - y.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := x) (b := y) hGe
    refine ⟨?_, ?_⟩
    · intro h
      simp [Tamago.Utils.FixedPointMathLib.dist, Contract.run, Verity.pure,
        Pure.pure,
        hBranch, hSubVal]
      omega
    · intro _h
      simp [Tamago.Utils.FixedPointMathLib.dist, Contract.run, Verity.pure,
        Pure.pure,
        hBranch, hSubVal]
      omega
  · have hLt : x.val < y.val := by omega
    have hNotBranch : ¬ x >= y := by
      exact Nat.not_le_of_gt hLt
    have hLe : x.val ≤ y.val := Nat.le_of_lt hLt
    have hSubVal : (sub y x).val = y.val - x.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := y) (b := x) hLe
    refine ⟨?_, ?_⟩
    · intro _h
      simp [Tamago.Utils.FixedPointMathLib.dist, Contract.run, Verity.pure,
        Pure.pure,
        hNotBranch, hSubVal]
      omega
    · intro h
      exact False.elim (hGe h)

theorem avg_returns_floor_average (x y : Uint256) (s : ContractState) :
    avg_property x y ((avg x y).run s).fst := by
  unfold avg_property
  by_cases hGe : y.val ≤ x.val
  · have hBranch : x >= y := hGe
    have hSubVal : (sub x y).val = x.val - y.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := x) (b := y) hGe
    have hDivVal : (div (sub x y) 2).val = (x.val - y.val) / 2 := by
      rw [div_two_val, hSubVal]
    have hAddLt :
        y.val + (div (sub x y) 2).val < Verity.Core.Uint256.modulus := by
      rw [hDivVal]
      have hDivLe : (x.val - y.val) / 2 ≤ x.val - y.val := Nat.div_le_self _ _
      have hBound : y.val + (x.val - y.val) / 2 ≤ x.val := by omega
      exact Nat.lt_of_le_of_lt hBound x.isLt
    have hAddVal :
        (add y (div (sub x y) 2)).val = y.val + (x.val - y.val) / 2 := by
      simpa [HAdd.hAdd, hDivVal] using
        Verity.Core.Uint256.add_eq_of_lt (a := y) (b := div (sub x y) 2) hAddLt
    have hRun :
        ((avg x y).run s).fst.val = y.val + (x.val - y.val) / 2 := by
      simp [avg, Contract.run, Verity.pure, Pure.pure, hBranch, hAddVal]
    constructor
    · rw [hRun]
      have hDivLower := two_mul_div_two_le (x.val - y.val)
      omega
    · rw [hRun]
      have hDivUpper := lt_two_mul_div_two_succ (x.val - y.val)
      omega
  · have hLt : x.val < y.val := by omega
    have hNotBranch : ¬ x >= y := Nat.not_le_of_gt hLt
    have hLe : x.val ≤ y.val := Nat.le_of_lt hLt
    have hSubVal : (sub y x).val = y.val - x.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := y) (b := x) hLe
    have hDivVal : (div (sub y x) 2).val = (y.val - x.val) / 2 := by
      rw [div_two_val, hSubVal]
    have hAddLt :
        x.val + (div (sub y x) 2).val < Verity.Core.Uint256.modulus := by
      rw [hDivVal]
      have hDivLe : (y.val - x.val) / 2 ≤ y.val - x.val := Nat.div_le_self _ _
      have hBound : x.val + (y.val - x.val) / 2 ≤ y.val := by omega
      exact Nat.lt_of_le_of_lt hBound y.isLt
    have hAddVal :
        (add x (div (sub y x) 2)).val = x.val + (y.val - x.val) / 2 := by
      simpa [HAdd.hAdd, hDivVal] using
        Verity.Core.Uint256.add_eq_of_lt (a := x) (b := div (sub y x) 2) hAddLt
    have hRun :
        ((avg x y).run s).fst.val = x.val + (y.val - x.val) / 2 := by
      simp [avg, Contract.run, Verity.pure, Pure.pure, hNotBranch, hAddVal]
    constructor
    · rw [hRun]
      have hDivLower := two_mul_div_two_le (y.val - x.val)
      omega
    · rw [hRun]
      have hDivUpper := lt_two_mul_div_two_succ (y.val - x.val)
      omega

private theorem mul_val_of_lt (a b : Uint256)
    (h : a.val * b.val < Verity.Core.Uint256.modulus) :
    (mul a b).val = a.val * b.val := by
  simpa [HMul.hMul] using Verity.Core.Uint256.mul_eq_of_lt (a := a) (b := b) h

private theorem sqrtStepUint_val
    (x zU : Uint256) (z : Nat)
    (hzVal : zU.val = z) (hzPos : 0 < z)
    (hAddLt : z + x.val / z < Verity.Core.Uint256.modulus) :
    (shr 1 (add zU (div x zU))).val = sqrtStep x.val z := by
  have hzUNe : zU.val ≠ 0 := by omega
  have hDivVal : (div x zU).val = x.val / z := by
    rw [div_val x zU hzUNe, hzVal]
  have hAddLtU : zU.val + (div x zU).val < Verity.Core.Uint256.modulus := by
    simpa [hzVal, hDivVal] using hAddLt
  have hAddVal : (add zU (div x zU)).val = z + x.val / z := by
    rw [add_val_of_lt _ _ hAddLtU, hzVal, hDivVal]
  unfold sqrtStep
  rw [shr_val, hAddVal]
  norm_num

private theorem sqrtFinishCorrectionUint_val
    (x zU : Uint256) (z : Nat)
    (hZVal : zU.val = z) (hzPos : 0 < z) :
    (sub zU (boolToWord (div x zU < zU))).val =
      z - if x.val / z < z then 1 else 0 := by
  have hzUNe : zU.val ≠ 0 := by omega
  have hDivVal : (div x zU).val = x.val / z := by
    rw [div_val x zU hzUNe, hZVal]
  have hBranchIff : (div x zU < zU) ↔ x.val / z < z := by
    change (div x zU).val < zU.val ↔ x.val / z < z
    rw [hDivVal, hZVal]
  by_cases h : x.val / z < z
  · have hUint := hBranchIff.mpr h
    simp [hUint, h, boolToWord]
    have hOne : (1 : Uint256).val = 1 := by simp
    have hSub : (sub zU 1).val = z - 1 := by
      have hLe : (1 : Uint256).val ≤ zU.val := by
        rw [hOne, hZVal]
        exact hzPos
      simpa [hZVal, hOne, HSub.hSub] using
        Verity.Core.Uint256.sub_eq_of_le (a := zU) (b := (1 : Uint256)) hLe
    exact hSub
  · have hUint : ¬ div x zU < zU := fun hh => h (hBranchIff.mp hh)
    have hFlag : boolToWord (div x zU < zU) = (0 : Uint256) := by
      simp [boolToWord, hUint]
    rw [hFlag, sub_zero_val]
    simp [h, hZVal]

private theorem sqrtInnerUint_val (x : Uint256) :
    (let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
     let z := shr 1 (sub 256 xClz)
     let z := shr 1 (add (shl z 1) (shr z x))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     z).val = innerSqrt x.val := by
  by_cases hx0 : x.val = 0
  · have hxEq : x = 0 := by
      apply Verity.Core.Uint256.ext
      simpa using hx0
    rw [hxEq]
    native_decide
  · have hxPos : 0 < x.val := Nat.pos_of_ne_zero hx0
    have hxLt : x.val < 2 ^ 256 := by
      simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
    let i : Fin 256 := ⟨Nat.log2 x.val, (Nat.log2_lt (Nat.ne_of_gt hxPos)).2 hxLt⟩
    let m := Nat.sqrt x.val
    have hmlo : m * m ≤ x.val := by simpa [m] using Nat.sqrt_le x.val
    have hmhi : x.val < (m + 1) * (m + 1) := by
      simpa [m] using Nat.lt_succ_sqrt x.val
    have hOct : 2 ^ i.val ≤ x.val ∧ x.val < 2 ^ (i.val + 1) := by
      have hlog :
          2 ^ Nat.log2 x.val ≤ x.val ∧ x.val < 2 ^ (Nat.log2 x.val + 1) := by
        constructor
        · simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.ne_of_gt hxPos)
        · simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
            Nat.lt_pow_succ_log_self (by decide : 1 < 2) x.val
      simpa [i] using hlog
    have hm : 0 < m := by
      by_cases hm0 : m = 0
      · have hx1 : 1 ≤ x.val := Nat.succ_le_of_lt hxPos
        have hlt1 : x.val < 1 := by
          have : x.val < (0 + 1) * (0 + 1) := by simpa [m, hm0] using hmhi
          simpa using this
        exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
      · exact Nat.pos_of_ne_zero hm0
    have hinterval : Sqrt.OctaveCert.loOf i ≤ m ∧ m ≤ Sqrt.OctaveCert.hiOf i :=
      m_within_cert_interval i x.val m hmlo hmhi hOct
    have hSeedEq : sqrtSeed x.val = Sqrt.OctaveCert.seedOf i :=
      sqrtSeed_eq_octaveSeed i x.val hOct
    let qU := shr 1 (sub 256 (Tamago.Proof.Utils.ClzProof.clzFormulaUint x))
    let z1U := shr 1 (add (shl qU 1) (shr qU x))
    let z2U := shr 1 (add z1U (div x z1U))
    let z3U := shr 1 (add z2U (div x z2U))
    let z4U := shr 1 (add z3U (div x z3U))
    let z5U := shr 1 (add z4U (div x z4U))
    let z6U := shr 1 (add z5U (div x z5U))
    let z0 := Sqrt.OctaveCert.seedOf i
    let z1 := sqrtStep x.val z0
    let z2 := sqrtStep x.val z1
    let z3 := sqrtStep x.val z2
    let z4 := sqrtStep x.val z3
    let z5 := sqrtStep x.val z4
    let z6 := sqrtStep x.val z5
    have hz1Val : z1U.val = z1 := by
      have h := sqrtFirstStepUint_val x hx0
      simpa [qU, z1U, z0, z1, hSeedEq] using h
    have hz0Pos : 0 < z0 := by
      simp [z0, Sqrt.OctaveCert.seedOf, Nat.shiftLeft_eq]
    have hmz1 : m ≤ z1 := by
      dsimp [z1, z0]
      exact sqrt_step_floor_bound x.val (Sqrt.OctaveCert.seedOf i) m hz0Pos hmlo
    have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
    have hmz2 : m ≤ z2 := by
      dsimp [z2]
      exact sqrt_step_floor_bound x.val z1 m hz1Pos hmlo
    have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
    have hmz3 : m ≤ z3 := by
      dsimp [z3]
      exact sqrt_step_floor_bound x.val z2 m hz2Pos hmlo
    have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
    have hmz4 : m ≤ z4 := by
      dsimp [z4]
      exact sqrt_step_floor_bound x.val z3 m hz3Pos hmlo
    have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
    have hmz5 : m ≤ z5 := by
      dsimp [z5]
      exact sqrt_step_floor_bound x.val z4 m hz4Pos hmlo
    have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
    have hrun5 := Sqrt.ErrorChain.run5_error_bounds i x.val m hm hmlo hmhi
      hinterval.1 hinterval.2
    have hd1 : z1 - m ≤ Sqrt.OctaveCert.d1 i := by
      simpa [z0, z1, z2, z3, z4, z5] using hrun5.1
    have hd2 : z2 - m ≤ Sqrt.OctaveCert.d2 i := by
      simpa [z0, z1, z2, z3, z4, z5] using hrun5.2.1
    have hd3 : z3 - m ≤ Sqrt.OctaveCert.d3 i := by
      simpa [z0, z1, z2, z3, z4, z5] using hrun5.2.2.1
    have hd4 : z4 - m ≤ Sqrt.OctaveCert.d4 i := by
      simpa [z0, z1, z2, z3, z4, z5] using hrun5.2.2.2.1
    have hd5 : z5 - m ≤ Sqrt.OctaveCert.d5 i := by
      simpa [z0, z1, z2, z3, z4, z5] using hrun5.2.2.2.2
    have hd1m : Sqrt.OctaveCert.d1 i ≤ m := Nat.le_trans (Sqrt.OctaveCert.d1_le_lo i) hinterval.1
    have hd2m : Sqrt.OctaveCert.d2 i ≤ m := Nat.le_trans (Sqrt.OctaveCert.d2_le_lo i) hinterval.1
    have hd3m : Sqrt.OctaveCert.d3 i ≤ m := Nat.le_trans (Sqrt.OctaveCert.d3_le_lo i) hinterval.1
    have hd4m : Sqrt.OctaveCert.d4 i ≤ m := Nat.le_trans (Sqrt.OctaveCert.d4_le_lo i) hinterval.1
    have hd5m : Sqrt.OctaveCert.d5 i ≤ m := Nat.le_trans (Sqrt.OctaveCert.d5_le_lo i) hinterval.1
    have hxMod : x.val < Verity.Core.Uint256.modulus := x.isLt
    have hsum1 : z1 + x.val / z1 < Verity.Core.Uint256.modulus :=
      sqrt_sum_lt_uint256_of_cert x.val m z1 (Sqrt.OctaveCert.d1 i)
        hxMod hm hmlo hmhi hmz1 hd1 hd1m
    have hsum2 : z2 + x.val / z2 < Verity.Core.Uint256.modulus :=
      sqrt_sum_lt_uint256_of_cert x.val m z2 (Sqrt.OctaveCert.d2 i)
        hxMod hm hmlo hmhi hmz2 hd2 hd2m
    have hsum3 : z3 + x.val / z3 < Verity.Core.Uint256.modulus :=
      sqrt_sum_lt_uint256_of_cert x.val m z3 (Sqrt.OctaveCert.d3 i)
        hxMod hm hmlo hmhi hmz3 hd3 hd3m
    have hsum4 : z4 + x.val / z4 < Verity.Core.Uint256.modulus :=
      sqrt_sum_lt_uint256_of_cert x.val m z4 (Sqrt.OctaveCert.d4 i)
        hxMod hm hmlo hmhi hmz4 hd4 hd4m
    have hsum5 : z5 + x.val / z5 < Verity.Core.Uint256.modulus :=
      sqrt_sum_lt_uint256_of_cert x.val m z5 (Sqrt.OctaveCert.d5 i)
        hxMod hm hmlo hmhi hmz5 hd5 hd5m
    have hz2Val : z2U.val = z2 := by
      have h := sqrtStepUint_val x z1U z1 hz1Val hz1Pos hsum1
      simpa [z2U, z2, sqrtStep] using h
    have hz3Val : z3U.val = z3 := by
      have h := sqrtStepUint_val x z2U z2 hz2Val hz2Pos hsum2
      simpa [z3U, z3, sqrtStep] using h
    have hz4Val : z4U.val = z4 := by
      have h := sqrtStepUint_val x z3U z3 hz3Val hz3Pos hsum3
      simpa [z4U, z4, sqrtStep] using h
    have hz5Val : z5U.val = z5 := by
      have h := sqrtStepUint_val x z4U z4 hz4Val hz4Pos hsum4
      simpa [z5U, z5, sqrtStep] using h
    have hz6Val : z6U.val = z6 := by
      have h := sqrtStepUint_val x z5U z5 hz5Val hz5Pos hsum5
      simpa [z6U, z6, sqrtStep] using h
    have hInner : innerSqrt x.val = z6 := by
      unfold innerSqrt
      simp [Nat.ne_of_gt hxPos, hSeedEq, z0, z1, z2, z3, z4, z5, z6]
    change z6U.val = innerSqrt x.val
    rw [hz6Val, hInner]

private theorem sqrtFloorCorrectionUint_val
    (x z : Uint256)
    (hZVal : z.val = innerSqrt x.val) :
    (sub z (boolToWord (div x z < z))).val = floorSqrt x.val := by
  by_cases hz0 : innerSqrt x.val = 0
  · have hzValZero : z.val = 0 := by simpa [hz0] using hZVal
    have hNot : ¬ div x z < z := by
      change ¬ (div x z).val < z.val
      omega
    unfold floorSqrt
    have hFlag : boolToWord (div x z < z) = (0 : Uint256) := by
      simp [boolToWord, hNot]
    rw [hFlag, sub_zero_val]
    simp [hz0, hzValZero]
  · have hzPos : 0 < innerSqrt x.val := Nat.pos_of_ne_zero hz0
    have h := sqrtFinishCorrectionUint_val x z (innerSqrt x.val) hZVal hzPos
    unfold floorSqrt
    simpa [hz0] using h

private theorem sqrtBodyUint_val (x : Uint256) :
    (let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
     let z := shr 1 (sub 256 xClz)
     let z := shr 1 (add (shl z 1) (shr z x))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     let z := shr 1 (add z (div x z))
     sub z (boolToWord (div x z < z))).val =
      floorSqrt x.val := by
  let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
  let z1 := shr 1 (sub 256 xClz)
  let z2 := shr 1 (add (shl z1 1) (shr z1 x))
  let z3 := shr 1 (add z2 (div x z2))
  let z4 := shr 1 (add z3 (div x z3))
  let z5 := shr 1 (add z4 (div x z4))
  let z6 := shr 1 (add z5 (div x z5))
  let z7 := shr 1 (add z6 (div x z6))
  have hInner : z7.val = innerSqrt x.val := by
    simpa [xClz, z1, z2, z3, z4, z5, z6, z7] using sqrtInnerUint_val x
  change (sub z7 (boolToWord (div x z7 < z7))).val = floorSqrt x.val
  exact sqrtFloorCorrectionUint_val x z7 hInner

private theorem sqrt_run_eq_floorSqrt (x : Uint256) (s : ContractState) :
    ((sqrt x).run s).fst.val = floorSqrt x.val := by
  rw [sqrt, Tamago.Utils.FixedPointMathLibBase.sqrt.eq_1]
  rw [monad_bind_success_run_fst _ _ (Tamago.Proof.Utils.ClzProof.clzFormulaUint x) s s
    (Tamago.Proof.Utils.ClzProof.clz_apply_eq_success x s)]
  let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
  let z1 := shr 1 (sub 256 xClz)
  let z2 := shr 1 (add (shl z1 1) (shr z1 x))
  let z3 := shr 1 (add z2 (div x z2))
  let z4 := shr 1 (add z3 (div x z3))
  let z5 := shr 1 (add z4 (div x z4))
  let z6 := shr 1 (add z5 (div x z5))
  let z7 := shr 1 (add z6 (div x z6))
  have hBody :
      (sub z7 (boolToWord (div x z7 < z7))).val = floorSqrt x.val := by
    simpa [xClz, z1, z2, z3, z4, z5, z6, z7] using sqrtBodyUint_val x
  change
      ((Verity.pure (sub z7 (boolToWord (div x z7 < z7)))).run s).fst.val =
        floorSqrt x.val
  simpa [Verity.pure, Pure.pure] using hBody

theorem sqrt_returns_math_floor (x : Uint256) (s : ContractState) :
    sqrt_property x ((sqrt x).run s).fst := by
  unfold sqrt_property
  rw [sqrt_run_eq_floorSqrt x s]
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  exact floorSqrt_correct_u256 x.val hxLt

private theorem uint3_val : (3 : Uint256).val = 3 := by
  native_decide

private theorem cbrt_square_no_overflow_of_le_three_pow86 {z : Nat}
    (hUpper : z ≤ 3 * 2 ^ 86) :
    z * z < Verity.Core.Uint256.modulus := by
  have hSq : z * z ≤ (3 * 2 ^ 86) * (3 * 2 ^ 86) :=
    Nat.mul_le_mul hUpper hUpper
  have hBound :
      (3 * 2 ^ 86) * (3 * 2 ^ 86) < Verity.Core.Uint256.modulus := by
    native_decide
  exact lt_of_le_of_lt hSq hBound

private theorem cbrtStepUint_val
    (x zU : Uint256) (z : Nat)
    (hzVal : zU.val = z) (hzPos : 0 < z)
    (hMulLt : z * z < Verity.Core.Uint256.modulus)
    (hAddLt : x.val / (z * z) + z + z < Verity.Core.Uint256.modulus) :
    (div (add (add (div x (mul zU zU)) zU) zU) 3).val =
      cbrtStep x.val z := by
  have hMulLtU : zU.val * zU.val < Verity.Core.Uint256.modulus := by
    simpa [hzVal] using hMulLt
  have hMulVal : (mul zU zU).val = z * z := by
    rw [mul_val_of_lt _ _ hMulLtU, hzVal]
  have hMulNe : (mul zU zU).val ≠ 0 := by
    rw [hMulVal]
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hDivVal : (div x (mul zU zU)).val = x.val / (z * z) := by
    rw [div_val x (mul zU zU) hMulNe, hMulVal]
  have hAdd1LtU : (div x (mul zU zU)).val + zU.val <
      Verity.Core.Uint256.modulus := by
    rw [hDivVal, hzVal]
    exact lt_of_le_of_lt (by omega : x.val / (z * z) + z ≤
      x.val / (z * z) + z + z) hAddLt
  have hAdd1Val : (add (div x (mul zU zU)) zU).val =
      x.val / (z * z) + z := by
    rw [add_val_of_lt _ _ hAdd1LtU, hDivVal, hzVal]
  have hAdd2LtU : (add (div x (mul zU zU)) zU).val + zU.val <
      Verity.Core.Uint256.modulus := by
    rw [hAdd1Val, hzVal]
    simpa [Nat.add_assoc] using hAddLt
  have hAdd2Val : (add (add (div x (mul zU zU)) zU) zU).val =
      x.val / (z * z) + z + z := by
    rw [add_val_of_lt _ _ hAdd2LtU, hAdd1Val, hzVal]
  have hThreeNe : (3 : Uint256).val ≠ 0 := by
    rw [uint3_val]
    norm_num
  unfold cbrtStep
  rw [div_val _ 3 hThreeNe, hAdd2Val, uint3_val]
  simp [two_mul, Nat.add_assoc]

private theorem cbrtStepUint_zero_of_zero (zU : Uint256) (hz : zU.val = 0) :
    (div (add (add (div (0 : Uint256) (mul zU zU)) zU) zU) 3).val = 0 := by
  have hzEq : zU = 0 := by
    apply Verity.Core.Uint256.ext
    simpa using hz
  subst zU
  native_decide

private theorem cbrtSeedUint_val_of_ne (x : Uint256) (hx0 : x.val ≠ 0) :
    (let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
     let b := sub 255 xClz
     let multiplierIndex := add 29 (mod b 3)
     let multiplier := byte multiplierIndex 0x90b5e5
     Contracts.bitOr 1 (shr 7 (shl (div b 3) multiplier))).val =
      cbrtSeed x.val := by
  let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
  let bU := sub 255 xClz
  let b := Nat.log2 x.val
  have hxPos : 0 < x.val := Nat.pos_of_ne_zero hx0
  have hx256 : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hClzVal : xClz.val = 255 - b := by
    simpa [xClz, b, hx0] using Tamago.Proof.Utils.ClzProof.clzFormulaUint_val x
  have hbLt256 : b < 256 := (Nat.log2_lt (Nat.ne_of_gt hxPos)).2 hx256
  have h255 : (255 : Uint256).val = 255 := by native_decide
  have hClzLe : xClz.val ≤ (255 : Uint256).val := by
    rw [h255, hClzVal]
    exact Nat.sub_le 255 b
  have hbVal : bU.val = b := by
    have h := Verity.Core.Uint256.sub_eq_of_le (a := (255 : Uint256)) (b := xClz) hClzLe
    have hRaw : (sub 255 xClz).val = (255 : Uint256).val - xClz.val := by
      simpa [HSub.hSub] using h
    change (sub 255 xClz).val = b
    rw [hRaw, h255, hClzVal]
    omega
  have hThree : (3 : Uint256).val = 3 := by native_decide
  have hDivBVal : (div bU 3).val = b / 3 := by
    rw [div_val bU 3 (by rw [hThree]; norm_num), hbVal, hThree]
  have hMultiplierVal :
      (byte (add 29 (mod bU 3)) 0x90b5e5).val = cbrtSeedMultiplier b :=
    cbrtPackedMultiplierByte_val bU b hbVal
  let multiplier := byte (add 29 (mod bU 3)) 0x90b5e5
  have hMultiplierLe : multiplier.val ≤ 229 := by
    rw [show multiplier.val = cbrtSeedMultiplier b by simpa [multiplier] using hMultiplierVal]
    unfold cbrtSeedMultiplier
    have hModLt : b % 3 < 3 := Nat.mod_lt b (by decide)
    have hCases : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hCases with h | h | h <;> simp [h]
  have hDivLe : b / 3 ≤ 85 := by omega
  have hShlLt : multiplier.val * 2 ^ (div bU 3).val <
      Verity.Core.Uint256.modulus := by
    rw [hDivBVal]
    have hPow : 2 ^ (b / 3) ≤ 2 ^ 85 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hDivLe
    have hMul : multiplier.val * 2 ^ (b / 3) ≤ 229 * 2 ^ 85 :=
      Nat.mul_le_mul hMultiplierLe hPow
    have hBound : 229 * 2 ^ 85 < Verity.Core.Uint256.modulus := by native_decide
    exact lt_of_le_of_lt hMul hBound
  have hShlVal : (shl (div bU 3) multiplier).val =
      cbrtSeedMultiplier b * 2 ^ (b / 3) := by
    have hMultiplierVal' : multiplier.val = cbrtSeedMultiplier b := by
      simpa [multiplier] using hMultiplierVal
    have hShlLt' :
        cbrtSeedMultiplier b * 2 ^ (b / 3) < Verity.Core.Uint256.modulus := by
      simpa [hMultiplierVal', hDivBVal] using hShlLt
    rw [shl_val, hMultiplierVal', hDivBVal]
    exact Nat.mod_eq_of_lt hShlLt'
  have hSeven : (7 : Uint256).val = 7 := by native_decide
  have hShrVal : (shr 7 (shl (div bU 3) multiplier)).val =
      (cbrtSeedMultiplier b * 2 ^ (b / 3)) / 2 ^ 7 := by
    rw [shr_val, hShlVal, hSeven]
  have hOrLt :
      Nat.lor (1 : Uint256).val (shr 7 (shl (div bU 3) multiplier)).val <
        Verity.Core.Uint256.modulus := by
    rw [uintOne_val, hShrVal]
    have hSeedLe :
        (cbrtSeedMultiplier b * 2 ^ (b / 3)) / 2 ^ 7 ≤ 229 * 2 ^ 85 := by
      have hPow : 2 ^ (b / 3) ≤ 2 ^ 85 :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) hDivLe
      have hMul : cbrtSeedMultiplier b * 2 ^ (b / 3) ≤ 229 * 2 ^ 85 := by
        have hMultLe : cbrtSeedMultiplier b ≤ 229 := by
          unfold cbrtSeedMultiplier
          have hModLt : b % 3 < 3 := Nat.mod_lt b (by decide)
          have hCases : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
          rcases hCases with h | h | h <;> simp [h]
        exact Nat.mul_le_mul hMultLe hPow
      exact le_trans (Nat.div_le_self _ _) hMul
    have hLorLe : Nat.lor 1 ((cbrtSeedMultiplier b * 2 ^ (b / 3)) / 2 ^ 7) <
        2 ^ 256 := by
      have hBound : 229 * 2 ^ 85 < 2 ^ 255 := by native_decide
      have hArgLt : ((cbrtSeedMultiplier b * 2 ^ (b / 3)) / 2 ^ 7) < 2 ^ 255 :=
        lt_of_le_of_lt hSeedLe hBound
      exact Nat.or_lt_two_pow
        (by native_decide : 1 < 2 ^ 256)
        (lt_trans hArgLt (by native_decide : 2 ^ 255 < 2 ^ 256))
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using hLorLe
  have hOrVal :
      (Contracts.bitOr 1 (shr 7 (shl (div bU 3) multiplier))).val =
        Nat.lor 1 ((cbrtSeedMultiplier b * 2 ^ (b / 3)) / 2 ^ 7) := by
    rw [bitOr_val_of_lt _ _ hOrLt, uintOne_val, hShrVal]
  unfold cbrtSeed
  change (Contracts.bitOr 1 (shr 7 (shl (div bU 3) multiplier))).val =
    1 ||| (cbrtSeedMultiplier (Nat.log2 x.val) <<< (Nat.log2 x.val / 3) >>> 7)
  rw [hOrVal]
  simp [b, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rfl

private theorem cbrtSeed_square_lt_word_cert (i : Fin 248) :
    Cbrt.OctaveCert.seedOf i * Cbrt.OctaveCert.seedOf i < Verity.Core.Uint256.modulus := by
  fin_cases i <;> native_decide

private theorem cbrtSeed_step_add_lt_word_cert (i : Fin 248) :
    2 ^ (i.val + Cbrt.OctaveCert.certOffset + 1) /
          (Cbrt.OctaveCert.seedOf i * Cbrt.OctaveCert.seedOf i) +
        Cbrt.OctaveCert.seedOf i + Cbrt.OctaveCert.seedOf i <
      Verity.Core.Uint256.modulus := by
  fin_cases i <;> native_decide

private theorem cbrtD1_upper_three_pow86_cert (i : Fin 248) :
    Cbrt.OctaveCert.hiOf i + Cbrt.OctaveCert.d1Of i ≤ 3 * 2 ^ 86 := by
  fin_cases i <;> native_decide

private theorem icbrt_lt_pow86 {x : Nat} (hxLt : x < 2 ^ 256) :
    icbrt x < 2 ^ 86 := by
  by_contra hNot
  have hLe : 2 ^ 86 ≤ icbrt x := Nat.le_of_not_lt hNot
  have hCubeGe :
      (2 ^ 86 : Nat) * 2 ^ 86 * 2 ^ 86 ≤
        icbrt x * icbrt x * icbrt x :=
    Nat.mul_le_mul (Nat.mul_le_mul hLe hLe) hLe
  have hPow : (2 ^ 86 : Nat) * 2 ^ 86 * 2 ^ 86 = 2 ^ (86 + 86 + 86) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
  have hFloor := icbrt_cube_le x
  have hGe : 2 ^ 256 ≤ x := by
    have h256 : (2 ^ 256 : Nat) ≤ 2 ^ (86 + 86 + 86) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (by norm_num)
    exact Nat.le_trans h256 (Nat.le_trans (by simpa [hPow] using hCubeGe) hFloor)
  exact (Nat.not_lt_of_ge hGe) hxLt

private theorem div_le_icbrt_add_six
    (x z : Nat) (haPos : 0 < icbrt x) (hFloor : icbrt x ≤ z) :
    x / (z * z) ≤ icbrt x + 6 := by
  let a := icbrt x
  have haaPos : 0 < a * a := Nat.mul_pos (by simpa [a] using haPos)
    (by simpa [a] using haPos)
  have hzz : a * a ≤ z * z := Nat.mul_le_mul hFloor hFloor
  have hDivMono : x / (z * z) ≤ x / (a * a) :=
    Nat.div_le_div_left hzz (by simpa [a] using haaPos)
  have hNextCube : x < (a + 1) * (a + 1) * (a + 1) := by
    simpa [a] using icbrt_lt_succ_cube x
  have hCubeBound : (a + 1) * (a + 1) * (a + 1) ≤ (a + 7) * (a * a) := by
    nlinarith [haPos]
  have hDivLt : x / (a * a) < a + 7 :=
    (Nat.div_lt_iff_lt_mul (by simpa [a] using haaPos)).2
      (lt_of_lt_of_le hNextCube hCubeBound)
  omega

private theorem cbrtStep_add_no_overflow
    (x z : Nat) (hxLt : x < 2 ^ 256) (haPos : 0 < icbrt x)
    (hFloor : icbrt x ≤ z) (hUpper : z ≤ 3 * 2 ^ 86) :
    x / (z * z) + z + z < Verity.Core.Uint256.modulus := by
  have hDivLe := div_le_icbrt_add_six x z haPos hFloor
  have hCbrtLt := icbrt_lt_pow86 (x := x) hxLt
  have hNumLe : x / (z * z) + z + z ≤ 7 * 2 ^ 86 + 6 := by omega
  have hBound : 7 * 2 ^ 86 + 6 < Verity.Core.Uint256.modulus := by
    native_decide
  exact lt_of_le_of_lt hNumLe hBound

private theorem cbrtStep_le_three_pow86
    (x z : Nat) (hxLt : x < 2 ^ 256) (haPos : 0 < icbrt x)
    (hFloor : icbrt x ≤ z) (hUpper : z ≤ 3 * 2 ^ 86) :
    cbrtStep x z ≤ 3 * 2 ^ 86 := by
  unfold cbrtStep
  have hDivLe := div_le_icbrt_add_six x z haPos hFloor
  have hCbrtLt := icbrt_lt_pow86 (x := x) hxLt
  have hNumLe : x / (z * z) + 2 * z ≤ 7 * 2 ^ 86 + 6 := by omega
  have hDiv : (x / (z * z) + 2 * z) / 3 ≤ (7 * 2 ^ 86 + 6) / 3 :=
    Nat.div_le_div_right hNumLe
  have hBound : (7 * 2 ^ 86 + 6) / 3 ≤ 3 * 2 ^ 86 := by
    native_decide
  exact le_trans hDiv hBound

private theorem cbrtFinishCorrectionUint_val
    (x zU : Uint256) (z : Nat)
    (hZVal : zU.val = z) (hzPos : 0 < z)
    (hMulLt : z * z < Verity.Core.Uint256.modulus) :
    (sub zU (boolToWord (div x (mul zU zU) < zU))).val =
      z - if x.val / (z * z) < z then 1 else 0 := by
  have hMulLtU : zU.val * zU.val < Verity.Core.Uint256.modulus := by
    simpa [hZVal] using hMulLt
  have hMulVal : (mul zU zU).val = z * z := by
    rw [mul_val_of_lt _ _ hMulLtU, hZVal]
  have hMulNe : (mul zU zU).val ≠ 0 := by
    rw [hMulVal]
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hDivVal : (div x (mul zU zU)).val = x.val / (z * z) := by
    rw [div_val x (mul zU zU) hMulNe, hMulVal]
  have hBranchIff : (div x (mul zU zU) < zU) ↔ x.val / (z * z) < z := by
    change (div x (mul zU zU)).val < zU.val ↔ x.val / (z * z) < z
    rw [hDivVal, hZVal]
  by_cases h : x.val / (z * z) < z
  · have hUint := hBranchIff.mpr h
    simp [hUint, h, boolToWord]
    have hOne : (1 : Uint256).val = 1 := by simp
    have hSub : (sub zU 1).val = z - 1 := by
      have hLe : (1 : Uint256).val ≤ zU.val := by
        rw [hOne, hZVal]
        exact hzPos
      simpa [hZVal, hOne, HSub.hSub] using
        Verity.Core.Uint256.sub_eq_of_le (a := zU) (b := (1 : Uint256)) hLe
    exact hSub
  · have hUint : ¬ div x (mul zU zU) < zU := fun hh => h (hBranchIff.mp hh)
    have hFlag : boolToWord (div x (mul zU zU) < zU) = (0 : Uint256) := by
      simp [boolToWord, hUint]
    rw [hFlag, sub_zero_val]
    simp [h, hZVal]

private def cbrtVerityRunVal (n : Nat) : Nat :=
  ((cbrt (uintOfNat n)).run defaultState).fst.val

private theorem cbrt_run_val_eq_cbrtVerityRunVal (n : Nat) (s : ContractState) :
    ((cbrt (uintOfNat n)).run s).fst.val = cbrtVerityRunVal n := rfl

private theorem cbrtVerityRunVal_small_eq_floorCbrt :
    ∀ v : Fin 256, v.val ≠ 0 → cbrtVerityRunVal v.val = floorCbrt v.val := by
  native_decide

private theorem cbrt_run_eq_floorCbrt_small_ne_zero
    (x : Fin 256) (hx0 : x.val ≠ 0) (s : ContractState) :
    ((cbrt (uintOfNat x.val)).run s).fst.val = floorCbrt x.val := by
  rw [cbrt_run_val_eq_cbrtVerityRunVal]
  exact cbrtVerityRunVal_small_eq_floorCbrt x hx0

private theorem cbrt_run_eq_floorCbrt_large
    (x : Uint256) (s : ContractState) (hxLarge : 2 ^ 8 ≤ x.val) :
    ((cbrt x).run s).fst.val = floorCbrt x.val := by
  have hxPos : 0 < x.val := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hxLarge
  have hx0 : x.val ≠ 0 := Nat.ne_of_gt hxPos
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hLogLower : 8 ≤ Nat.log2 x.val := by
    by_cases h : 8 ≤ Nat.log2 x.val
    · exact h
    · have hlt : Nat.log2 x.val + 1 ≤ 8 := by omega
      have hOctHi : x.val < 2 ^ (Nat.log2 x.val + 1) := by
        simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self (by decide : 1 < 2) x.val
      have hPow : 2 ^ (Nat.log2 x.val + 1) ≤ 2 ^ 8 :=
        Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) hlt
      have : x.val < 2 ^ 8 := Nat.lt_of_lt_of_le hOctHi hPow
      omega
  have hLogLt : Nat.log2 x.val < 256 :=
    (Nat.log2_lt (Nat.ne_of_gt hxPos)).2 hxLt
  let i : Fin 248 := ⟨Nat.log2 x.val - Cbrt.OctaveCert.certOffset, by
    dsimp [Cbrt.OctaveCert.certOffset]
    omega⟩
  have hIdx : i.val + Cbrt.OctaveCert.certOffset = Nat.log2 x.val := by
    dsimp [i, Cbrt.OctaveCert.certOffset]
    omega
  have hOct :
      2 ^ (i.val + Cbrt.OctaveCert.certOffset) ≤ x.val ∧
        x.val < 2 ^ (i.val + Cbrt.OctaveCert.certOffset + 1) := by
    rw [hIdx]
    constructor
    · simpa [Nat.log2_eq_log_two] using
        Nat.pow_log_le_self 2 (Nat.ne_of_gt hxPos)
    · simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by decide : 1 < 2) x.val
  let m := icbrt x.val
  have hmlo : m * m * m ≤ x.val := by
    simpa [m] using icbrt_cube_le x.val
  have hmhi : x.val < (m + 1) * (m + 1) * (m + 1) := by
    simpa [m] using icbrt_lt_succ_cube x.val
  have hInterval := Cbrt.Wiring.m_within_cert_interval i x.val m hmlo hmhi hOct
  have hmPos : 0 < m := lt_of_lt_of_le (Cbrt.OctaveCert.lo_pos i) hInterval.1
  have hm2 : 2 ≤ m := Nat.le_trans (Cbrt.OctaveCert.lo_ge_two i) hInterval.1
  have hSeedEq : cbrtSeed x.val = Cbrt.OctaveCert.seedOf i :=
    Cbrt.Wiring.cbrtSeed_eq_octaveSeed i x.val hOct
  rw [cbrt, Tamago.Utils.FixedPointMathLibBase.cbrt.eq_1]
  rw [monad_bind_success_run_fst _ _ (Tamago.Proof.Utils.ClzProof.clzFormulaUint x) s s
    (Tamago.Proof.Utils.ClzProof.clz_apply_eq_success x s)]
  let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint x
  let bU := sub 255 xClz
  let multiplierIndex := add 29 (mod bU 3)
  let multiplier := byte multiplierIndex 0x90b5e5
  let z0U := Contracts.bitOr 1 (shr 7 (shl (div bU 3) multiplier))
  let stepU : Uint256 → Uint256 := fun z =>
    div (add (add (div x (mul z z)) z) z) 3
  let z1U := stepU z0U
  let z2U := stepU z1U
  let z3U := stepU z2U
  let z4U := stepU z3U
  let z5U := stepU z4U
  let z0 := cbrtSeed x.val
  let z1 := cbrtStep x.val z0
  let z2 := cbrtStep x.val z1
  let z3 := cbrtStep x.val z2
  let z4 := cbrtStep x.val z3
  let z5 := cbrtStep x.val z4
  have hz0Val : z0U.val = z0 := by
    simpa [xClz, bU, multiplierIndex, multiplier, z0U, z0] using
      cbrtSeedUint_val_of_ne x hx0
  have hz0Pos : 0 < z0 := by
    simpa [z0] using cbrtSeed_pos x.val
  have hz0MulLt : z0 * z0 < Verity.Core.Uint256.modulus := by
    simpa [z0, hSeedEq] using cbrtSeed_square_lt_word_cert i
  have hz0AddLt : x.val / (z0 * z0) + z0 + z0 <
      Verity.Core.Uint256.modulus := by
    have hDivLe :
        x.val / (z0 * z0) ≤
          2 ^ (i.val + Cbrt.OctaveCert.certOffset + 1) /
            (Cbrt.OctaveCert.seedOf i * Cbrt.OctaveCert.seedOf i) := by
      have hxLe : x.val ≤ 2 ^ (i.val + Cbrt.OctaveCert.certOffset + 1) :=
        Nat.le_of_lt hOct.2
      simpa [z0, hSeedEq] using Nat.div_le_div_right hxLe
    have hCert := cbrtSeed_step_add_lt_word_cert i
    omega
  have hz1Val : z1U.val = z1 := by
    simpa [stepU, z1U, z0U, z0, z1] using
      cbrtStepUint_val x z0U z0 hz0Val hz0Pos hz0MulLt hz0AddLt
  have hz1Floor : m ≤ z1 := by
    simpa [m, z0, z1] using
      cbrt_step_floor_bound x.val z0 m hz0Pos hmlo
  have hz1D : z1 - m ≤ Cbrt.OctaveCert.d1Of i := by
    have h := Cbrt.ErrorChain.cbrt_d1_bound x.val m (Cbrt.OctaveCert.seedOf i)
      (Cbrt.OctaveCert.loOf i) (Cbrt.OctaveCert.hiOf i)
      (Cbrt.OctaveCert.seed_pos i) hmlo hmhi hInterval.1 hInterval.2
    simp only at h
    have hd1eq := Cbrt.OctaveCert.d1_eq i
    have hmaxeq := Cbrt.OctaveCert.maxabs_eq i
    rw [hmaxeq] at hd1eq
    rw [← hd1eq] at h
    simpa [z1, z0, hSeedEq] using h
  have hz1Upper : z1 ≤ 3 * 2 ^ 86 := by
    have hle : z1 ≤ m + Cbrt.OctaveCert.d1Of i := (Nat.sub_le_iff_le_add').1 hz1D
    have hCert := cbrtD1_upper_three_pow86_cert i
    omega
  have hicbrtPos : 0 < icbrt x.val := by simpa [m] using hmPos
  have hz1Pos : 0 < z1 := lt_of_lt_of_le hmPos hz1Floor
  have hz1MulLt : z1 * z1 < Verity.Core.Uint256.modulus :=
    cbrt_square_no_overflow_of_le_three_pow86 hz1Upper
  have hz1AddLt : x.val / (z1 * z1) + z1 + z1 < Verity.Core.Uint256.modulus :=
    cbrtStep_add_no_overflow x.val z1 hxLt hicbrtPos (by simpa [m] using hz1Floor) hz1Upper
  have hz2Val : z2U.val = z2 := by
    simpa [stepU, z2U, z1U, z1, z2] using
      cbrtStepUint_val x z1U z1 hz1Val hz1Pos hz1MulLt hz1AddLt
  have hz2Floor : m ≤ z2 := by
    simpa [m, z1, z2] using
      cbrt_step_floor_bound x.val z1 m hz1Pos hmlo
  have hz2Upper : z2 ≤ 3 * 2 ^ 86 :=
    cbrtStep_le_three_pow86 x.val z1 hxLt hicbrtPos (by simpa [m] using hz1Floor) hz1Upper
  have hz2Pos : 0 < z2 := lt_of_lt_of_le hmPos hz2Floor
  have hz2MulLt : z2 * z2 < Verity.Core.Uint256.modulus :=
    cbrt_square_no_overflow_of_le_three_pow86 hz2Upper
  have hz2AddLt : x.val / (z2 * z2) + z2 + z2 < Verity.Core.Uint256.modulus :=
    cbrtStep_add_no_overflow x.val z2 hxLt hicbrtPos (by simpa [m] using hz2Floor) hz2Upper
  have hz3Val : z3U.val = z3 := by
    simpa [stepU, z3U, z2U, z2, z3] using
      cbrtStepUint_val x z2U z2 hz2Val hz2Pos hz2MulLt hz2AddLt
  have hz3Floor : m ≤ z3 := by
    simpa [m, z2, z3] using
      cbrt_step_floor_bound x.val z2 m hz2Pos hmlo
  have hz3Upper : z3 ≤ 3 * 2 ^ 86 :=
    cbrtStep_le_three_pow86 x.val z2 hxLt hicbrtPos (by simpa [m] using hz2Floor) hz2Upper
  have hz3Pos : 0 < z3 := lt_of_lt_of_le hmPos hz3Floor
  have hz3MulLt : z3 * z3 < Verity.Core.Uint256.modulus :=
    cbrt_square_no_overflow_of_le_three_pow86 hz3Upper
  have hz3AddLt : x.val / (z3 * z3) + z3 + z3 < Verity.Core.Uint256.modulus :=
    cbrtStep_add_no_overflow x.val z3 hxLt hicbrtPos (by simpa [m] using hz3Floor) hz3Upper
  have hz4Val : z4U.val = z4 := by
    simpa [stepU, z4U, z3U, z3, z4] using
      cbrtStepUint_val x z3U z3 hz3Val hz3Pos hz3MulLt hz3AddLt
  have hz4Floor : m ≤ z4 := by
    simpa [m, z3, z4] using
      cbrt_step_floor_bound x.val z3 m hz3Pos hmlo
  have hz4Upper : z4 ≤ 3 * 2 ^ 86 :=
    cbrtStep_le_three_pow86 x.val z3 hxLt hicbrtPos (by simpa [m] using hz3Floor) hz3Upper
  have hz4Pos : 0 < z4 := lt_of_lt_of_le hmPos hz4Floor
  have hz4MulLt : z4 * z4 < Verity.Core.Uint256.modulus :=
    cbrt_square_no_overflow_of_le_three_pow86 hz4Upper
  have hz4AddLt : x.val / (z4 * z4) + z4 + z4 < Verity.Core.Uint256.modulus :=
    cbrtStep_add_no_overflow x.val z4 hxLt hicbrtPos (by simpa [m] using hz4Floor) hz4Upper
  have hz5Val : z5U.val = z5 := by
    simpa [stepU, z5U, z4U, z4, z5] using
      cbrtStepUint_val x z4U z4 hz4Val hz4Pos hz4MulLt hz4AddLt
  have hInner : innerCbrt x.val = z5 := by
    unfold innerCbrt
    simp [z0, z1, z2, z3, z4, z5]
  have hz5ValInner : z5U.val = innerCbrt x.val := by
    rw [hz5Val, ← hInner]
  have hz5Pos : 0 < innerCbrt x.val := innerCbrt_pos x.val hxPos
  have hz5MulLt : innerCbrt x.val * innerCbrt x.val < Verity.Core.Uint256.modulus := by
    have hCube := Cbrt.OverflowSafety.innerCbrt_cube_lt_word x.val hxPos hxLt
    have hOne : 1 ≤ innerCbrt x.val := Nat.succ_le_of_lt hz5Pos
    have hSqLeCube :
        innerCbrt x.val * innerCbrt x.val ≤
          innerCbrt x.val * (innerCbrt x.val * innerCbrt x.val) := by
      calc
        innerCbrt x.val * innerCbrt x.val =
            1 * (innerCbrt x.val * innerCbrt x.val) := by rw [Nat.one_mul]
        _ ≤ innerCbrt x.val * (innerCbrt x.val * innerCbrt x.val) :=
            Nat.mul_le_mul_right _ hOne
    exact lt_of_le_of_lt hSqLeCube
      (by simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using hCube)
  change
      ((Verity.pure
          (sub z5U (boolToWord (div x (mul z5U z5U) < z5U)))).run s).fst.val =
        floorCbrt x.val
  have hFinish := cbrtFinishCorrectionUint_val x z5U (innerCbrt x.val)
    hz5ValInner hz5Pos hz5MulLt
  unfold floorCbrt
  simpa [Verity.pure, Pure.pure] using hFinish

private theorem cbrt_run_eq_floorCbrt (x : Uint256) (s : ContractState) :
    ((cbrt x).run s).fst.val = floorCbrt x.val := by
  by_cases hx0 : x.val = 0
  · have hxEq : x = 0 := by
      apply Verity.Core.Uint256.ext
      simpa using hx0
    rw [hxEq]
    rw [cbrt, Tamago.Utils.FixedPointMathLibBase.cbrt.eq_1]
    rw [monad_bind_success_run_fst _ _
      (Tamago.Proof.Utils.ClzProof.clzFormulaUint (0 : Uint256)) s s
      (Tamago.Proof.Utils.ClzProof.clz_apply_eq_success (0 : Uint256) s)]
    let xU : Uint256 := 0
    let xClz := Tamago.Proof.Utils.ClzProof.clzFormulaUint xU
    let bU := sub 255 xClz
    let multiplierIndex := add 29 (mod bU 3)
    let multiplier := byte multiplierIndex 0x90b5e5
    let z0U := Contracts.bitOr 1 (shr 7 (shl (div bU 3) multiplier))
    let stepU : Uint256 → Uint256 := fun z =>
      div (add (add (div xU (mul z z)) z) z) 3
    let z1U := stepU z0U
    let z2U := stepU z1U
    let z3U := stepU z2U
    let z4U := stepU z3U
    let z5U := stepU z4U
    change
        ((Verity.pure
            (sub z5U (boolToWord (div xU (mul z5U z5U) < z5U)))).run s).fst.val =
          floorCbrt 0
    have hClzVal : xClz.val = 256 := by
      simpa [xU] using Tamago.Proof.Utils.ClzProof.clzFormulaUint_val (0 : Uint256)
    have hBVal : bU.val = Verity.Core.Uint256.modulus - 1 := by
      have h255 : (255 : Uint256).val = 255 := by native_decide
      have hGt : xClz.val > (255 : Uint256).val := by
        rw [hClzVal, h255]
        norm_num
      have h := Verity.Core.Uint256.sub_val_of_gt (a := (255 : Uint256)) (b := xClz) hGt
      rw [h, hClzVal, h255]
      simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    have hThree : (3 : Uint256).val = 3 := by native_decide
    have hDivBVal : (div bU 3).val = bU.val / 3 := by
      rw [div_val bU 3 (by rw [hThree]; norm_num), hThree]
    have hShiftGe : 256 ≤ (div bU 3).val := by
      rw [hDivBVal, hBVal]
      native_decide
    have hShlZero : (shl (div bU 3) multiplier).val = 0 :=
      shl_zero_of_shift_ge_256 (div bU 3) multiplier hShiftGe
    have hSeven : (7 : Uint256).val = 7 := by native_decide
    have hShrZero : (shr 7 (shl (div bU 3) multiplier)).val = 0 := by
      rw [shr_val, hShlZero, hSeven]
      norm_num
    have hz0Val : z0U.val = 1 := by
      rw [show z0U = Contracts.bitOr 1 (shr 7 (shl (div bU 3) multiplier)) by rfl]
      rw [bitOr_val, uintOne_val, hShrZero]
      native_decide
    have hz1Val : z1U.val = 0 := by
      have hStep := cbrtStepUint_val xU z0U 1 hz0Val
        (by norm_num)
        (by rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]; native_decide)
        (by native_decide)
      simpa [stepU, z1U, cbrtStep, xU] using hStep
    have hz2Val : z2U.val = 0 := by
      simpa [stepU, z2U, z1U, xU] using cbrtStepUint_zero_of_zero z1U hz1Val
    have hz3Val : z3U.val = 0 := by
      simpa [stepU, z3U, z2U, xU] using cbrtStepUint_zero_of_zero z2U hz2Val
    have hz4Val : z4U.val = 0 := by
      simpa [stepU, z4U, z3U, xU] using cbrtStepUint_zero_of_zero z3U hz3Val
    have hz5Val : z5U.val = 0 := by
      simpa [stepU, z5U, z4U, xU] using cbrtStepUint_zero_of_zero z4U hz4Val
    have hNot : ¬ div xU (mul z5U z5U) < z5U := by
      change ¬ (div xU (mul z5U z5U)).val < z5U.val
      rw [hz5Val]
      exact Nat.not_lt_zero _
    have hFloor0 : floorCbrt 0 = 0 := by native_decide
    rw [hFloor0]
    have hFlag : boolToWord (div xU (mul z5U z5U) < z5U) = (0 : Uint256) := by
      simp [boolToWord, hNot]
    rw [hFlag]
    have hpure (a : Uint256) : ((Verity.pure a).run s).fst.val = a.val := rfl
    rw [hpure]
    rw [sub_zero_val, hz5Val]
  · by_cases hxSmall : x.val < 256
    · have hxEq : x = uintOfNat x.val := by
        apply Verity.Core.Uint256.ext
        simp [uintOfNat_val_of_lt x.isLt]
      calc
        ((cbrt x).run s).fst.val =
            ((cbrt (uintOfNat x.val)).run s).fst.val :=
              congrArg (fun y : Uint256 => ((cbrt y).run s).fst.val) hxEq
        _ = floorCbrt x.val :=
            cbrt_run_eq_floorCbrt_small_ne_zero ⟨x.val, hxSmall⟩ hx0 s
    · have hxLarge : 2 ^ 8 ≤ x.val := by
        norm_num at hxSmall
        omega
      exact cbrt_run_eq_floorCbrt_large x s hxLarge

theorem cbrt_returns_math_floor (x : Uint256) (s : ContractState) :
    cbrt_property x ((cbrt x).run s).fst := by
  unfold cbrt_property
  rw [cbrt_run_eq_floorCbrt x s]
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  exact Cbrt.Correctness.floorCbrt_correct_u256_all x.val hxLt

private def log2Search : Nat → Nat → Nat → Nat
  | 0, r, value => if 1 < value then r + 1 else r
  | level + 1, r, value =>
      let shift := 2 ^ (level + 1)
      if 2 ^ shift - 1 < value then
        log2Search level (r + shift) (value / 2 ^ shift)
      else
        log2Search level r value

private theorem log2Search_bounds
    (level n r value : Nat)
    (hValue : value = n / 2 ^ r)
    (hLower : n ≠ 0 → 2 ^ r ≤ n)
    (hBound : value < 2 ^ (2 ^ (level + 1))) :
    (n ≠ 0 → 2 ^ log2Search level r value ≤ n) ∧
      n < 2 ^ (log2Search level r value + 1) := by
  induction level generalizing r value with
  | zero =>
      simp [log2Search]
      by_cases hBranch : 1 < value
      · simp [hBranch]
        constructor
        · intro _hn
          have hTwoLe : 2 ≤ value := hBranch
          rw [hValue] at hTwoLe
          have hMul : 2 ^ r * 2 ≤ n := by
            have hMul' : 2 * 2 ^ r ≤ n :=
              (Nat.le_div_iff_mul_le (k := 2 ^ r)
                (Nat.pow_pos (by decide : 0 < 2))).1 hTwoLe
            simpa [Nat.mul_comm] using hMul'
          simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hMul
        · have hUpper0 : n < 2 ^ r * (value + 1) := by
            rw [hValue]
            exact Nat.lt_mul_div_succ n (Nat.pow_pos (by decide : 0 < 2))
          have hValueLe : value + 1 ≤ 4 := by omega
          have hUpper1 : 2 ^ r * (value + 1) ≤ 2 ^ r * 4 :=
            Nat.mul_le_mul_left _ hValueLe
          have hUpper2 : 2 ^ r * 4 = 2 ^ (r + 2) := by
            norm_num [Nat.pow_add, Nat.mul_assoc]
          have hGoalPow : 2 ^ (r + 2) = 2 ^ (r + 1 + 1) := by
            congr 1
          omega
      · simp [hBranch]
        constructor
        · exact hLower
        · have hUpper0 : n < 2 ^ r * (value + 1) := by
            rw [hValue]
            exact Nat.lt_mul_div_succ n (Nat.pow_pos (by decide : 0 < 2))
          have hValueLe : value + 1 ≤ 2 := by omega
          have hUpper1 : 2 ^ r * (value + 1) ≤ 2 ^ r * 2 :=
            Nat.mul_le_mul_left _ hValueLe
          have hUpper2 : 2 ^ r * 2 = 2 ^ (r + 1) := by
            rw [Nat.pow_succ]
          omega
  | succ level ih =>
      simp [log2Search]
      by_cases hBranch : 2 ^ 2 ^ (level + 1) - 1 < value
      · simp [hBranch]
        let shift := 2 ^ (level + 1)
        have hStepValue :
            value / 2 ^ shift = n / 2 ^ (r + shift) := by
          rw [hValue, Nat.div_div_eq_div_mul, Nat.pow_add]
        have hStepLower : n ≠ 0 → 2 ^ (r + shift) ≤ n := by
          intro _hn
          have hBranch' : 2 ^ shift - 1 < value := by
            simpa [shift] using hBranch
          have hLe : 2 ^ shift ≤ value := by omega
          rw [hValue] at hLe
          have hMul : 2 ^ r * 2 ^ shift ≤ n := by
            have hMul' : 2 ^ shift * 2 ^ r ≤ n :=
              (Nat.le_div_iff_mul_le (k := 2 ^ r)
                (Nat.pow_pos (by decide : 0 < 2))).1 hLe
            simpa [Nat.mul_comm] using hMul'
          simpa [Nat.pow_add] using hMul
        have hStepBound : value / 2 ^ shift < 2 ^ (2 ^ (level + 1)) := by
          have hInit : value < 2 ^ (shift + shift) := by
            have hExp : 2 ^ (level + 1 + 1) = shift + shift := by
              simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
            simpa [hExp] using hBound
          have hMul : 2 ^ (shift + shift) = 2 ^ shift * 2 ^ shift := by
            rw [Nat.pow_add]
          rw [hMul] at hInit
          simpa [shift] using Nat.div_lt_of_lt_mul hInit
        exact ih (r + shift) (value / 2 ^ shift) hStepValue hStepLower hStepBound
      · simp [hBranch]
        have hNextBound : value < 2 ^ (2 ^ (level + 1)) := by
          have hBranch' : ¬ 2 ^ 2 ^ (level + 1) - 1 < value := hBranch
          have hPowPos : 0 < 2 ^ 2 ^ (level + 1) := Nat.pow_pos (by decide : 0 < 2)
          omega
        exact ih r value hValue hLower hNextBound

private theorem log2Search_initial_bounds (n : Nat) (hnLt : n < 2 ^ 256) :
    (n ≠ 0 → 2 ^ log2Search 7 0 n ≤ n) ∧
      n < 2 ^ (log2Search 7 0 n + 1) := by
  apply log2Search_bounds 7 n 0 n
  · simp
  · intro hn
    exact Nat.pos_of_ne_zero hn
  · simpa using hnLt

private def log2SearchContract : Nat → Uint256 → Uint256 → Contract Uint256
  | 0, r, value =>
      if (uintOfNat 1) < value then Pure.pure (add r (uintOfNat 1)) else Pure.pure r
  | level + 1, r, value =>
      let shift := 2 ^ (level + 1)
      if (uintOfNat (2 ^ shift - 1)) < value then
        log2SearchContract level (add r (uintOfNat shift)) (shr (uintOfNat shift) value)
      else
        log2SearchContract level r value

private theorem log2_eq_searchContract (x : Uint256) :
    Tamago.Utils.FixedPointMathLibBase.log2 x = log2SearchContract 7 0 x := by
  simp [Tamago.Utils.FixedPointMathLibBase.log2, log2SearchContract, uintOfNat,
    Bind.bind, Pure.pure, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]

private theorem log2SearchContract_val
    (level : Nat) (r value : Uint256) (s : ContractState)
    (hRMax : r.val + (2 ^ (level + 1) - 1) ≤ 255) :
    ((log2SearchContract level r value).run s).fst.val =
      log2Search level r.val value.val := by
  induction level generalizing r value with
  | zero =>
      have hR1Lt : r.val + 1 < Verity.Core.Uint256.modulus := by
        have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
        rw [hMod]
        omega
      have hOneLt : 1 < Verity.Core.Uint256.modulus := by
        rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
        norm_num
      have hOneVal : (uintOfNat 1).val = 1 := uintOfNat_val_of_lt hOneLt
      by_cases hBranch : (uintOfNat 1).val < value.val
      · have hNatBranch : 1 < value.val := by simpa [hOneVal] using hBranch
        simp [log2SearchContract, log2Search, Contract.run, Pure.pure,
          Verity.pure, ContractResult.fst, hBranch, hNatBranch]
        exact add_small_val r hR1Lt
      · have hNatBranch : ¬ 1 < value.val := by simpa [hOneVal] using hBranch
        simp [log2SearchContract, log2Search, Contract.run, Pure.pure,
          Verity.pure, ContractResult.fst, hBranch, hNatBranch]
  | succ level ih =>
      by_cases hBranch : uintOfNat (2 ^ 2 ^ (level + 1) - 1) < value
      · let shift := 2 ^ (level + 1)
        have hThresholdLt :
            2 ^ shift - 1 < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftLe : shift ≤ 255 := by
            have hMax : 2 ^ (level + 1 + 1) - 1 ≤ 255 := by omega
            have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
              have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
                simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
              have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
              rw [hDouble]
              omega
            exact le_trans hShiftPart hMax
          have hPowLe : 2 ^ shift ≤ 2 ^ 255 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) hShiftLe
          have hPowLt : 2 ^ shift < 2 ^ 256 :=
            lt_of_le_of_lt hPowLe (by norm_num : 2 ^ 255 < 2 ^ 256)
          have hPowPos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
          omega
        have hNatBranch : 2 ^ shift - 1 < value.val := by
          have hValBranch : (uintOfNat (2 ^ 2 ^ (level + 1) - 1)).val < value.val := hBranch
          simpa [shift, uintOfNat_val_of_lt hThresholdLt] using hValBranch
        have hShiftLt : shift < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftLe : shift ≤ 255 := by
            have hMax : 2 ^ (level + 1 + 1) - 1 ≤ 255 := by omega
            have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
              have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
                simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
              have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
              rw [hDouble]
              omega
            exact le_trans hShiftPart hMax
          omega
        have hAddLt : r.val + shift < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
            have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
            have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
              simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
            rw [hDouble]
            omega
          have hLe : r.val + shift ≤ 255 := by omega
          have h255 : 255 < 2 ^ 256 := by norm_num
          omega
        have hRecMax :
            (add r (uintOfNat shift)).val + (2 ^ (level + 1) - 1) ≤ 255 := by
          rw [add_small_val r hAddLt]
          have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
            simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
          omega
        have hShr : (shr (uintOfNat shift) value).val = value.val / 2 ^ shift := by
          rw [shr_val, uintOfNat_val_of_lt hShiftLt]
        simp only [log2SearchContract, log2Search, hBranch, shift, hNatBranch, if_true]
        have hRec := ih (add r (uintOfNat shift)) (shr (uintOfNat shift) value) hRecMax
        simpa [shift, add_small_val r hAddLt, hShr] using hRec
      · let shift := 2 ^ (level + 1)
        have hThresholdLt :
            2 ^ shift - 1 < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftLe : shift ≤ 255 := by
            have hMax : 2 ^ (level + 1 + 1) - 1 ≤ 255 := by omega
            have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
              have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
                simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
              have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
              rw [hDouble]
              omega
            exact le_trans hShiftPart hMax
          have hPowLe : 2 ^ shift ≤ 2 ^ 255 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) hShiftLe
          have hPowLt : 2 ^ shift < 2 ^ 256 :=
            lt_of_le_of_lt hPowLe (by norm_num : 2 ^ 255 < 2 ^ 256)
          have hPowPos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
          omega
        have hNatBranch : ¬ 2 ^ shift - 1 < value.val := by
          have hValBranch : ¬ (uintOfNat (2 ^ 2 ^ (level + 1) - 1)).val < value.val := by
            simpa using hBranch
          simpa [shift, uintOfNat_val_of_lt hThresholdLt] using hValBranch
        have hRecMax : r.val + (2 ^ (level + 1) - 1) ≤ 255 := by
          have hDouble : 2 ^ (level + 1 + 1) = 2 ^ (level + 1) + 2 ^ (level + 1) := by
            simp [Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
          omega
        simp only [log2SearchContract, log2Search, hBranch, shift, hNatBranch, if_false]
        exact ih r value hRecMax

private theorem log2_run_eq_search (x : Uint256) (s : ContractState) :
    ((log2 x).run s).fst.val = log2Search 7 0 x.val := by
  rw [log2, log2_eq_searchContract x]
  exact log2SearchContract_val 7 0 x s (by norm_num)

private def log2UpSearch (level x r value : Nat) : Nat :=
  let floor := log2Search level r value
  if 2 ^ floor < x then floor + 1 else floor

private def log2UpSearchContract : Nat → Uint256 → Uint256 → Uint256 → Contract Uint256
  | 0, x, r, value => do
      let mut r := r
      if (uintOfNat 1) < value then
        r := add r (uintOfNat 1)
      else
        Pure.pure ()
      if shl r (uintOfNat 1) < x then
        Pure.pure (add r (uintOfNat 1))
      else
        Pure.pure r
  | level + 1, x, r, value =>
      let shift := 2 ^ (level + 1)
      if (uintOfNat (2 ^ shift - 1)) < value then
        log2UpSearchContract level x (add r (uintOfNat shift)) (shr (uintOfNat shift) value)
      else
        log2UpSearchContract level x r value

private theorem log2Up_eq_searchContract (x : Uint256) :
    Tamago.Utils.FixedPointMathLibBase.log2Up x = log2UpSearchContract 7 x 0 x := by
  simp [Tamago.Utils.FixedPointMathLibBase.log2Up, log2UpSearchContract, uintOfNat,
    Bind.bind, Pure.pure, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]

private theorem log2UpSearchContract_val
    (level : Nat) (x r value : Uint256) (s : ContractState)
    (hRMax : r.val + (2 ^ (level + 1) - 1) ≤ 255)
    (hFloorMax : log2Search level r.val value.val ≤ 255) :
    ((log2UpSearchContract level x r value).run s).fst.val =
      log2UpSearch level x.val r.val value.val := by
  induction level generalizing r value with
  | zero =>
      have hOneLt : 1 < Verity.Core.Uint256.modulus := by
        rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
        norm_num
      have hOneVal : (uintOfNat 1).val = 1 := uintOfNat_val_of_lt hOneLt
      by_cases hBranch : (uintOfNat 1).val < value.val
      · have hNatBranch : 1 < value.val := by simpa [hOneVal] using hBranch
        have hAdd : (add r (uintOfNat 1)).val = r.val + 1 :=
          add_small_val r (by
            rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
            omega)
        have hFloorLe : r.val + 1 ≤ 255 := by
          simpa [log2Search, hNatBranch] using hFloorMax
        have hPowLt : 2 ^ (r.val + 1) < Verity.Core.Uint256.modulus := by
          rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
          exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
        have hShl :
            (shl (add r (uintOfNat 1)) (uintOfNat 1)).val = 2 ^ (r.val + 1) := by
          rw [shl_val, hAdd, hOneVal]
          simp [Nat.mod_eq_of_lt hPowLt]
        by_cases hRound : (shl (add r (uintOfNat 1)) (uintOfNat 1)).val < x.val
        · have hNatRound : 2 ^ (r.val + 1) < x.val := by simpa [hShl] using hRound
          have hAddRound :
              (add (add r (uintOfNat 1)) (uintOfNat 1)).val = r.val + 2 := by
            rw [add_small_val (add r (uintOfNat 1)) (by
              rw [hAdd]
              rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
              omega), hAdd]
          simp [log2UpSearchContract, log2UpSearch, log2Search, Contract.run,
            Bind.bind, Pure.pure, Verity.pure, hBranch, hNatBranch, hRound,
            hNatRound, hAddRound]
        · have hNatRound : ¬ 2 ^ (r.val + 1) < x.val := by simpa [hShl] using hRound
          simp [log2UpSearchContract, log2UpSearch, log2Search, Contract.run,
            Bind.bind, Pure.pure, Verity.pure, hBranch, hNatBranch, hRound,
            hNatRound, hAdd]
      · have hNatBranch : ¬ 1 < value.val := by simpa [hOneVal] using hBranch
        have hFloorLe : r.val ≤ 255 := by
          simpa [log2Search, hNatBranch] using hFloorMax
        have hPowLt : 2 ^ r.val < Verity.Core.Uint256.modulus := by
          rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
          exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
        have hShl : (shl r (uintOfNat 1)).val = 2 ^ r.val := by
          rw [shl_val, hOneVal]
          simp [Nat.mod_eq_of_lt hPowLt]
        by_cases hRound : (shl r (uintOfNat 1)).val < x.val
        · have hNatRound : 2 ^ r.val < x.val := by simpa [hShl] using hRound
          have hAddRound : (add r (uintOfNat 1)).val = r.val + 1 :=
            add_small_val r (by
              rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
              omega)
          simp [log2UpSearchContract, log2UpSearch, log2Search, Contract.run,
            Bind.bind, Pure.pure, Verity.pure, hBranch, hNatBranch, hRound,
            hNatRound, hAddRound]
        · have hNatRound : ¬ 2 ^ r.val < x.val := by simpa [hShl] using hRound
          simp [log2UpSearchContract, log2UpSearch, log2Search, Contract.run,
            Bind.bind, Pure.pure, Verity.pure, hBranch, hNatBranch, hRound,
            hNatRound]
  | succ level ih =>
      by_cases hBranch : uintOfNat (2 ^ 2 ^ (level + 1) - 1) < value
      · let shift := 2 ^ (level + 1)
        have hThresholdLt :
            2 ^ shift - 1 < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftLe : shift ≤ 255 := by
            have hMax : 2 ^ (level + 1 + 1) - 1 ≤ 255 := by omega
            have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
              have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
                simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
              have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
              rw [hDouble]
              omega
            exact le_trans hShiftPart hMax
          have hPowLe : 2 ^ shift ≤ 2 ^ 255 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) hShiftLe
          have hPowLt : 2 ^ shift < 2 ^ 256 :=
            lt_of_le_of_lt hPowLe (by norm_num : 2 ^ 255 < 2 ^ 256)
          have hPowPos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
          omega
        have hNatBranch : 2 ^ shift - 1 < value.val := by
          have hValBranch : (uintOfNat (2 ^ 2 ^ (level + 1) - 1)).val < value.val := hBranch
          simpa [shift, uintOfNat_val_of_lt hThresholdLt] using hValBranch
        have hShiftLt : shift < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftLe : shift ≤ 255 := by
            have hMax : 2 ^ (level + 1 + 1) - 1 ≤ 255 := by omega
            have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
              have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
                simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
              have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
              rw [hDouble]
              omega
            exact le_trans hShiftPart hMax
          omega
        have hAddLt : r.val + shift < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
            have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
            have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
              simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
            rw [hDouble]
            omega
          have hLe : r.val + shift ≤ 255 := by omega
          have h255 : 255 < 2 ^ 256 := by norm_num
          omega
        have hRecMax :
            (add r (uintOfNat shift)).val + (2 ^ (level + 1) - 1) ≤ 255 := by
          rw [add_small_val r hAddLt]
          have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
            simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
          omega
        have hShr : (shr (uintOfNat shift) value).val = value.val / 2 ^ shift := by
          rw [shr_val, uintOfNat_val_of_lt hShiftLt]
        have hRecFloorMax :
            log2Search level (add r (uintOfNat shift)).val
              (shr (uintOfNat shift) value).val ≤ 255 := by
          simpa [log2Search, hNatBranch, shift, add_small_val r hAddLt, hShr]
            using hFloorMax
        simp only [log2UpSearchContract, log2UpSearch, log2Search, hBranch,
          shift, hNatBranch, if_true]
        have hRec := ih (add r (uintOfNat shift)) (shr (uintOfNat shift) value)
          hRecMax hRecFloorMax
        simpa [log2UpSearch, log2Search, hNatBranch, shift, add_small_val r hAddLt,
          hShr] using hRec
      · let shift := 2 ^ (level + 1)
        have hThresholdLt :
            2 ^ shift - 1 < Verity.Core.Uint256.modulus := by
          have hMod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
          rw [hMod]
          have hShiftLe : shift ≤ 255 := by
            have hMax : 2 ^ (level + 1 + 1) - 1 ≤ 255 := by omega
            have hShiftPart : shift ≤ 2 ^ (level + 1 + 1) - 1 := by
              have hDouble : 2 ^ (level + 1 + 1) = shift + shift := by
                simp [shift, Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
              have hShiftPos : 0 < shift := Nat.pow_pos (by decide : 0 < 2)
              rw [hDouble]
              omega
            exact le_trans hShiftPart hMax
          have hPowLe : 2 ^ shift ≤ 2 ^ 255 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) hShiftLe
          have hPowLt : 2 ^ shift < 2 ^ 256 :=
            lt_of_le_of_lt hPowLe (by norm_num : 2 ^ 255 < 2 ^ 256)
          have hPowPos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
          omega
        have hNatBranch : ¬ 2 ^ shift - 1 < value.val := by
          have hValBranch : ¬ (uintOfNat (2 ^ 2 ^ (level + 1) - 1)).val < value.val := by
            simpa using hBranch
          simpa [shift, uintOfNat_val_of_lt hThresholdLt] using hValBranch
        have hRecMax : r.val + (2 ^ (level + 1) - 1) ≤ 255 := by
          have hDouble : 2 ^ (level + 1 + 1) = 2 ^ (level + 1) + 2 ^ (level + 1) := by
            simp [Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
          omega
        have hRecFloorMax :
            log2Search level r.val value.val ≤ 255 := by
          simpa [log2Search, hNatBranch, shift] using hFloorMax
        simp only [log2UpSearchContract, log2UpSearch, log2Search, hBranch,
          shift, hNatBranch, if_false]
        exact ih r value hRecMax hRecFloorMax

private theorem log2Search_initial_le_255 (x : Uint256) :
    log2Search 7 0 x.val ≤ 255 := by
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  by_cases hZero : x.val = 0
  · rw [hZero]
    norm_num [log2Search]
  · have hBounds := log2Search_initial_bounds x.val hxLt
    have hPowLt : 2 ^ log2Search 7 0 x.val < 2 ^ 256 :=
      lt_of_le_of_lt (hBounds.1 hZero) hxLt
    have hExpLt : log2Search 7 0 x.val < 256 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hPowLt
    omega

private theorem log2Up_run_eq_search (x : Uint256) (s : ContractState) :
    ((log2Up x).run s).fst.val = log2UpSearch 7 x.val 0 x.val := by
  rw [log2Up, log2Up_eq_searchContract x]
  exact log2UpSearchContract_val 7 x 0 x s (by norm_num)
    (log2Search_initial_le_255 x)

private def log10Final (r value : Nat) : Nat :=
  let r1 := if 9 < value then r + 1 else r
  let r2 := if 99 < value then r1 + 1 else r1
  let r3 := if 999 < value then r2 + 1 else r2
  if 9999 < value then r3 + 1 else r3

private theorem log10Final_bounds
    (n r value : Nat)
    (hValue : value = n / 10 ^ r)
    (hLower : n ≠ 0 → 10 ^ r ≤ n)
    (hBound : value < 10 ^ 5) :
    (n ≠ 0 → 10 ^ log10Final r value ≤ n) ∧
      n < 10 ^ (log10Final r value + 1) := by
  have lower_of {k : Nat} (hk : 10 ^ k ≤ value) : 10 ^ (r + k) ≤ n := by
    rw [hValue] at hk
    have hMul' : 10 ^ k * 10 ^ r ≤ n :=
      (Nat.le_div_iff_mul_le (k := 10 ^ r)
        (Nat.pow_pos (by decide : 0 < 10))).1 hk
    simpa [Nat.pow_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hMul'
  have upper_of {k : Nat} (hk : value + 1 ≤ 10 ^ k) :
      n < 10 ^ (r + k) := by
    have hUpper0 : n < 10 ^ r * (value + 1) := by
      rw [hValue]
      exact Nat.lt_mul_div_succ n (Nat.pow_pos (by decide : 0 < 10))
    have hUpper1 : 10 ^ r * (value + 1) ≤ 10 ^ r * 10 ^ k :=
      Nat.mul_le_mul_left _ hk
    have hUpper2 : 10 ^ r * 10 ^ k = 10 ^ (r + k) := by
      rw [Nat.pow_add]
    omega
  by_cases h4 : 9999 < value
  · have h1 : 9 < value := by omega
    have h2 : 99 < value := by omega
    have h3 : 999 < value := by omega
    simp [log10Final, h1, h2, h3, h4]
    constructor
    · intro _hn
      convert lower_of (k := 4) (by norm_num at h4 ⊢; omega) using 1
    · convert upper_of (k := 5) (by norm_num at hBound ⊢; omega) using 1
  · by_cases h3 : 999 < value
    · have h1 : 9 < value := by omega
      have h2 : 99 < value := by omega
      simp [log10Final, h1, h2, h3, h4]
      constructor
      · intro _hn
        convert lower_of (k := 3) (by norm_num at h3 ⊢; omega) using 1
      · convert upper_of (k := 4) (by norm_num at h4 ⊢; omega) using 1
    · by_cases h2 : 99 < value
      · have h1 : 9 < value := by omega
        simp [log10Final, h1, h2, h3, h4]
        constructor
        · intro _hn
          convert lower_of (k := 2) (by norm_num at h2 ⊢; omega) using 1
        · convert upper_of (k := 3) (by norm_num at h3 ⊢; omega) using 1
      · by_cases h1 : 9 < value
        · simp [log10Final, h1, h2, h3, h4]
          constructor
          · intro _hn
            convert lower_of (k := 1) (by norm_num at h1 ⊢; omega) using 1
          · convert upper_of (k := 2) (by norm_num at h2 ⊢; omega) using 1
        · simp [log10Final, h1, h2, h3, h4]
          constructor
          · exact hLower
          · convert upper_of (k := 1) (by norm_num at h1 ⊢; omega) using 1

private def log10Search0 (r value : Nat) : Nat :=
  log10Final r value

private def log10Search1 (r value : Nat) : Nat :=
  if 10 ^ 5 - 1 < value then
    log10Search0 (r + 5) (value / 10 ^ 5)
  else
    log10Search0 r value

private def log10Search2 (r value : Nat) : Nat :=
  if 10 ^ 10 - 1 < value then
    log10Search1 (r + 10) (value / 10 ^ 10)
  else
    log10Search1 r value

private def log10Search3 (r value : Nat) : Nat :=
  if 10 ^ 20 - 1 < value then
    log10Search2 (r + 20) (value / 10 ^ 20)
  else
    log10Search2 r value

private def log10Search4 (r value : Nat) : Nat :=
  if 10 ^ 38 - 1 < value then
    log10Search3 (r + 38) (value / 10 ^ 38)
  else
    log10Search3 r value

private theorem log10Search1_bounds
    (n r value : Nat)
    (hValue : value = n / 10 ^ r)
    (hLower : n ≠ 0 → 10 ^ r ≤ n)
    (hBound : value < 10 ^ 10) :
    (n ≠ 0 → 10 ^ log10Search1 r value ≤ n) ∧
      n < 10 ^ (log10Search1 r value + 1) := by
  unfold log10Search1 log10Search0
  by_cases hBranch : 10 ^ 5 - 1 < value
  · have hBranch' : 99999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hStepValue : value / 100000 = n / 10 ^ (r + 5) := by
      rw [hValue, Nat.div_div_eq_div_mul]
      norm_num [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hStepLower : n ≠ 0 → 10 ^ (r + 5) ≤ n := by
      intro _hn
      have hLe : 10 ^ 5 ≤ value := by omega
      rw [hValue] at hLe
      have hMul' : 10 ^ 5 * 10 ^ r ≤ n :=
        (Nat.le_div_iff_mul_le (k := 10 ^ r)
          (Nat.pow_pos (by decide : 0 < 10))).1 hLe
      simpa [Nat.pow_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hMul'
    have hStepBound : value / 100000 < 10 ^ 5 := by
      have hPow : 10 ^ 10 = 10 ^ 5 * 100000 := by norm_num
      rw [hPow] at hBound
      exact Nat.div_lt_of_lt_mul hBound
    exact log10Final_bounds n (r + 5) (value / 100000)
      hStepValue hStepLower hStepBound
  · have hBranch' : ¬ 99999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hSmall : value < 10 ^ 5 := by omega
    exact log10Final_bounds n r value hValue hLower hSmall

private theorem log10Search2_bounds
    (n r value : Nat)
    (hValue : value = n / 10 ^ r)
    (hLower : n ≠ 0 → 10 ^ r ≤ n)
    (hBound : value < 10 ^ 20) :
    (n ≠ 0 → 10 ^ log10Search2 r value ≤ n) ∧
      n < 10 ^ (log10Search2 r value + 1) := by
  unfold log10Search2
  by_cases hBranch : 10 ^ 10 - 1 < value
  · have hBranch' : 9999999999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hStepValue : value / 10000000000 = n / 10 ^ (r + 10) := by
      rw [hValue, Nat.div_div_eq_div_mul]
      norm_num [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hStepLower : n ≠ 0 → 10 ^ (r + 10) ≤ n := by
      intro _hn
      have hLe : 10 ^ 10 ≤ value := by omega
      rw [hValue] at hLe
      have hMul' : 10 ^ 10 * 10 ^ r ≤ n :=
        (Nat.le_div_iff_mul_le (k := 10 ^ r)
          (Nat.pow_pos (by decide : 0 < 10))).1 hLe
      simpa [Nat.pow_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hMul'
    have hStepBound : value / 10000000000 < 10 ^ 10 := by
      have hPow : 10 ^ 20 = 10 ^ 10 * 10000000000 := by norm_num
      rw [hPow] at hBound
      exact Nat.div_lt_of_lt_mul hBound
    exact log10Search1_bounds n (r + 10) (value / 10000000000)
      hStepValue hStepLower hStepBound
  · have hBranch' : ¬ 9999999999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hSmall : value < 10 ^ 10 := by omega
    exact log10Search1_bounds n r value hValue hLower hSmall

private theorem log10Search3_bounds
    (n r value : Nat)
    (hValue : value = n / 10 ^ r)
    (hLower : n ≠ 0 → 10 ^ r ≤ n)
    (hBound : value < 10 ^ 40) :
    (n ≠ 0 → 10 ^ log10Search3 r value ≤ n) ∧
      n < 10 ^ (log10Search3 r value + 1) := by
  unfold log10Search3
  by_cases hBranch : 10 ^ 20 - 1 < value
  · have hBranch' : 99999999999999999999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hStepValue :
        value / 100000000000000000000 = n / 10 ^ (r + 20) := by
      rw [hValue, Nat.div_div_eq_div_mul]
      norm_num [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hStepLower : n ≠ 0 → 10 ^ (r + 20) ≤ n := by
      intro _hn
      have hLe : 10 ^ 20 ≤ value := by omega
      rw [hValue] at hLe
      have hMul' : 10 ^ 20 * 10 ^ r ≤ n :=
        (Nat.le_div_iff_mul_le (k := 10 ^ r)
          (Nat.pow_pos (by decide : 0 < 10))).1 hLe
      simpa [Nat.pow_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hMul'
    have hStepBound : value / 100000000000000000000 < 10 ^ 20 := by
      have hPow : 10 ^ 40 = 10 ^ 20 * 100000000000000000000 := by norm_num
      rw [hPow] at hBound
      exact Nat.div_lt_of_lt_mul hBound
    exact log10Search2_bounds n (r + 20) (value / 100000000000000000000)
      hStepValue hStepLower hStepBound
  · have hBranch' : ¬ 99999999999999999999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hSmall : value < 10 ^ 20 := by omega
    exact log10Search2_bounds n r value hValue hLower hSmall

private theorem log10Search4_bounds
    (n r value : Nat)
    (hValue : value = n / 10 ^ r)
    (hLower : n ≠ 0 → 10 ^ r ≤ n)
    (hBound : value < 10 ^ 78) :
    (n ≠ 0 → 10 ^ log10Search4 r value ≤ n) ∧
      n < 10 ^ (log10Search4 r value + 1) := by
  unfold log10Search4
  by_cases hBranch : 10 ^ 38 - 1 < value
  · have hBranch' :
        99999999999999999999999999999999999999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hStepValue :
        value / 100000000000000000000000000000000000000 =
          n / 10 ^ (r + 38) := by
      rw [hValue, Nat.div_div_eq_div_mul]
      norm_num [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hStepLower : n ≠ 0 → 10 ^ (r + 38) ≤ n := by
      intro _hn
      have hLe : 10 ^ 38 ≤ value := by omega
      rw [hValue] at hLe
      have hMul' : 10 ^ 38 * 10 ^ r ≤ n :=
        (Nat.le_div_iff_mul_le (k := 10 ^ r)
          (Nat.pow_pos (by decide : 0 < 10))).1 hLe
      simpa [Nat.pow_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hMul'
    have hStepBound :
        value / 100000000000000000000000000000000000000 < 10 ^ 40 := by
      have hPow :
          10 ^ 78 = 10 ^ 40 * 100000000000000000000000000000000000000 := by
        norm_num
      rw [hPow] at hBound
      exact Nat.div_lt_of_lt_mul hBound
    exact log10Search3_bounds n (r + 38)
      (value / 100000000000000000000000000000000000000)
      hStepValue hStepLower hStepBound
  · have hBranch' :
        ¬ 99999999999999999999999999999999999999 < value := by
      norm_num at hBranch ⊢
      exact hBranch
    simp [hBranch']
    have hSmall : value < 10 ^ 40 := by omega
    exact log10Search3_bounds n r value hValue hLower hSmall

private theorem log10Search_initial_bounds (n : Nat) (hnLt : n < 10 ^ 78) :
    (n ≠ 0 → 10 ^ log10Search4 0 n ≤ n) ∧
      n < 10 ^ (log10Search4 0 n + 1) := by
  apply log10Search4_bounds n 0 n
  · simp
  · intro hn
    exact Nat.pos_of_ne_zero hn
  · exact hnLt

private def log10FinalContract3 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat 9999) < value then
    Pure.pure (add r (uintOfNat 1))
  else
    Pure.pure r

private def log10FinalContract2 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat 999) < value then
    have r := add r (uintOfNat 1)
    do
      let y ← Pure.pure PUnit.unit
      (fun _ => log10FinalContract3 r value) y
  else
    do
      let y ← Pure.pure ()
      (fun _ => log10FinalContract3 r value) y

private def log10FinalContract1 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat 99) < value then
    have r := add r (uintOfNat 1)
    do
      let y ← Pure.pure PUnit.unit
      (fun _ => log10FinalContract2 r value) y
  else
    do
      let y ← Pure.pure ()
      (fun _ => log10FinalContract2 r value) y

private def log10FinalContract (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat 9) < value then
    have r := add r (uintOfNat 1)
    do
      let y ← Pure.pure PUnit.unit
      (fun _ => log10FinalContract1 r value) y
  else
    do
      let y ← Pure.pure ()
      (fun _ => log10FinalContract1 r value) y

private def log10SearchContract0 (r value : Uint256) : Contract Uint256 :=
  log10FinalContract r value

private def log10SearchContract1 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat (10 ^ 5 - 1)) < value then
    log10SearchContract0 (add r (uintOfNat 5)) (div value (uintOfNat (10 ^ 5)))
  else
    log10SearchContract0 r value

private def log10SearchContract2 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat (10 ^ 10 - 1)) < value then
    log10SearchContract1 (add r (uintOfNat 10)) (div value (uintOfNat (10 ^ 10)))
  else
    log10SearchContract1 r value

private def log10SearchContract3 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat (10 ^ 20 - 1)) < value then
    log10SearchContract2 (add r (uintOfNat 20)) (div value (uintOfNat (10 ^ 20)))
  else
    log10SearchContract2 r value

private def log10SearchContract4 (r value : Uint256) : Contract Uint256 :=
  if (uintOfNat (10 ^ 38 - 1)) < value then
    log10SearchContract3 (add r (uintOfNat 38)) (div value (uintOfNat (10 ^ 38)))
  else
    log10SearchContract3 r value

private theorem log10_eq_searchContract (x : Uint256) :
    Tamago.Utils.FixedPointMathLibBase.log10 x = log10SearchContract4 0 x := by
  simp [Tamago.Utils.FixedPointMathLibBase.log10, log10SearchContract4,
    log10SearchContract3, log10SearchContract2, log10SearchContract1,
    log10SearchContract0, log10FinalContract, log10FinalContract1,
    log10FinalContract2, log10FinalContract3, uintOfNat, Bind.bind,
    Pure.pure, add, div, Verity.Core.Uint256.add, Verity.Core.Uint256.div,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]

private theorem log10FinalContract_success
    (r value : Uint256) (s : ContractState) :
    (log10FinalContract r value).run s =
      ContractResult.success ((log10FinalContract r value).run s).fst s := by
  simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
    log10FinalContract3, Contract.run, Bind.bind, Pure.pure]
  split_ifs <;> simp [Verity.pure, ContractResult.fst]

private theorem log10SearchContract1_success
    (r value : Uint256) (s : ContractState) :
    (log10SearchContract1 r value).run s =
      ContractResult.success ((log10SearchContract1 r value).run s).fst s := by
  unfold log10SearchContract1 log10SearchContract0
  split_ifs <;> exact log10FinalContract_success _ _ s

private theorem log10SearchContract2_success
    (r value : Uint256) (s : ContractState) :
    (log10SearchContract2 r value).run s =
      ContractResult.success ((log10SearchContract2 r value).run s).fst s := by
  unfold log10SearchContract2
  split_ifs <;> exact log10SearchContract1_success _ _ s

private theorem log10SearchContract3_success
    (r value : Uint256) (s : ContractState) :
    (log10SearchContract3 r value).run s =
      ContractResult.success ((log10SearchContract3 r value).run s).fst s := by
  unfold log10SearchContract3
  split_ifs <;> exact log10SearchContract2_success _ _ s

private theorem log10SearchContract4_success
    (r value : Uint256) (s : ContractState) :
    (log10SearchContract4 r value).run s =
      ContractResult.success ((log10SearchContract4 r value).run s).fst s := by
  unfold log10SearchContract4
  split_ifs <;> exact log10SearchContract3_success _ _ s

private theorem log10FinalContract_val
    (r value : Uint256) (s : ContractState)
    (hRMax : r.val + 4 < Verity.Core.Uint256.modulus) :
    ((log10FinalContract r value).run s).fst.val =
      log10Final r.val value.val := by
  have h9Lt : 9 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have h99Lt : 99 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have h999Lt : 999 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have h9999Lt : 9999 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have h9Val : (uintOfNat 9).val = 9 := uintOfNat_val_of_lt h9Lt
  have h99Val : (uintOfNat 99).val = 99 := uintOfNat_val_of_lt h99Lt
  have h999Val : (uintOfNat 999).val = 999 := uintOfNat_val_of_lt h999Lt
  have h9999Val : (uintOfNat 9999).val = 9999 := uintOfNat_val_of_lt h9999Lt
  by_cases h1 : (uintOfNat 9).val < value.val
  · have hn1 : 9 < value.val := by simpa [h9Val] using h1
    have hAdd1 : (add r (uintOfNat 1)).val = r.val + 1 := by
      exact add_small_val r (by omega)
    by_cases h2 : (uintOfNat 99).val < value.val
    · have hn2 : 99 < value.val := by simpa [h99Val] using h2
      have hAdd2 :
          (add (add r (uintOfNat 1)) (uintOfNat 1)).val = r.val + 2 := by
        rw [add_small_val (add r (uintOfNat 1)) (by rw [hAdd1]; omega), hAdd1]
      by_cases h3 : (uintOfNat 999).val < value.val
      · have hn3 : 999 < value.val := by simpa [h999Val] using h3
        have hAdd3 :
            (add (add (add r (uintOfNat 1)) (uintOfNat 1)) (uintOfNat 1)).val =
              r.val + 3 := by
          rw [add_small_val
            (add (add r (uintOfNat 1)) (uintOfNat 1)) (by rw [hAdd2]; omega), hAdd2]
        by_cases h4 : (uintOfNat 9999).val < value.val
        · have hn4 : 9999 < value.val := by simpa [h9999Val] using h4
          have hAdd4 :
              (add
                (add (add (add r (uintOfNat 1)) (uintOfNat 1)) (uintOfNat 1))
                (uintOfNat 1)).val = r.val + 4 := by
            rw [add_small_val
              (add (add (add r (uintOfNat 1)) (uintOfNat 1)) (uintOfNat 1))
              (by rw [hAdd3]; omega), hAdd3]
          simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd4]
        · have hn4 : ¬ 9999 < value.val := by simpa [h9999Val] using h4
          simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd3]
      · have hn3 : ¬ 999 < value.val := by simpa [h999Val] using h3
        have hn4 : ¬ 9999 < value.val := by omega
        by_cases h4 : (uintOfNat 9999).val < value.val
        · have hn4' : 9999 < value.val := by simpa [h9999Val] using h4
          exact False.elim (hn4 hn4')
        · simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd2]
    · have hn2 : ¬ 99 < value.val := by simpa [h99Val] using h2
      have hn3 : ¬ 999 < value.val := by omega
      have hn4 : ¬ 9999 < value.val := by omega
      by_cases h3 : (uintOfNat 999).val < value.val
      · have hn3' : 999 < value.val := by simpa [h999Val] using h3
        exact False.elim (hn3 hn3')
      · by_cases h4 : (uintOfNat 9999).val < value.val
        · have hn4' : 9999 < value.val := by simpa [h9999Val] using h4
          exact False.elim (hn4 hn4')
        · simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd1]
  · have hn1 : ¬ 9 < value.val := by simpa [h9Val] using h1
    have hn2 : ¬ 99 < value.val := by omega
    have hn3 : ¬ 999 < value.val := by omega
    have hn4 : ¬ 9999 < value.val := by omega
    by_cases h2 : (uintOfNat 99).val < value.val
    · have hn2' : 99 < value.val := by simpa [h99Val] using h2
      exact False.elim (hn2 hn2')
    · by_cases h3 : (uintOfNat 999).val < value.val
      · have hn3' : 999 < value.val := by simpa [h999Val] using h3
        exact False.elim (hn3 hn3')
      · by_cases h4 : (uintOfNat 9999).val < value.val
        · have hn4' : 9999 < value.val := by simpa [h9999Val] using h4
          exact False.elim (hn4 hn4')
        · simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4]

private theorem div_uintOfNat_val (value : Uint256) {n : Nat}
    (hnLt : n < Verity.Core.Uint256.modulus) (hnNe : n ≠ 0) :
    (div value (uintOfNat n)).val = value.val / n := by
  rw [div_val value (uintOfNat n) (by rw [uintOfNat_val_of_lt hnLt]; exact hnNe),
    uintOfNat_val_of_lt hnLt]

private theorem log10SearchContract1_val
    (r value : Uint256) (s : ContractState)
    (hRMax : r.val + 9 < Verity.Core.Uint256.modulus) :
    ((log10SearchContract1 r value).run s).fst.val =
      log10Search1 r.val value.val := by
  have hThresholdLt : 99999 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hDivisorLt : 100000 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hThresholdVal : (uintOfNat (10 ^ 5 - 1)).val = 99999 := by
    norm_num [uintOfNat_val_of_lt hThresholdLt]
  by_cases hBranch : uintOfNat (10 ^ 5 - 1) < value
  · have hValBranch : (uintOfNat (10 ^ 5 - 1)).val < value.val := hBranch
    have hNatBranch : 99999 < value.val := by simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : 10 ^ 5 - 1 < value.val := by
      norm_num
      exact hNatBranch
    have hAdd : (add r (uintOfNat 5)).val = r.val + 5 :=
      add_small_val r (by omega)
    have hDiv : (div value (uintOfNat 100000)).val = value.val / 100000 := by
      norm_num [div_uintOfNat_val value hDivisorLt (by norm_num)]
    have hFinal := log10FinalContract_val
      (add r (uintOfNat 5)) (div value (uintOfNat 100000)) s (by rw [hAdd]; omega)
    simp only [log10SearchContract1, log10Search1, log10Search0, hBranch, if_true]
    simpa [log10SearchContract0, hAdd, hDiv, hNatBranch, hNatBranchRaw] using hFinal
  · have hValBranch : ¬ (uintOfNat (10 ^ 5 - 1)).val < value.val := by
      simpa using hBranch
    have hNatBranch : ¬ 99999 < value.val := by simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 5 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hFinal := log10FinalContract_val r value s (by omega)
    simp only [log10SearchContract1, log10Search1, log10Search0, hBranch, if_false]
    simpa [log10SearchContract0, hNatBranch, hNatBranchRaw] using hFinal

private theorem log10SearchContract2_val
    (r value : Uint256) (s : ContractState)
    (hRMax : r.val + 19 < Verity.Core.Uint256.modulus) :
    ((log10SearchContract2 r value).run s).fst.val =
      log10Search2 r.val value.val := by
  have hThresholdLt : 9999999999 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hDivisorLt : 10000000000 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hThresholdVal : (uintOfNat (10 ^ 10 - 1)).val = 9999999999 := by
    norm_num [uintOfNat_val_of_lt hThresholdLt]
  by_cases hBranch : uintOfNat (10 ^ 10 - 1) < value
  · have hValBranch : (uintOfNat (10 ^ 10 - 1)).val < value.val := hBranch
    have hNatBranch : 9999999999 < value.val := by simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : 10 ^ 10 - 1 < value.val := by
      norm_num
      exact hNatBranch
    have hAdd : (add r (uintOfNat 10)).val = r.val + 10 :=
      add_small_val r (by omega)
    have hDiv : (div value (uintOfNat 10000000000)).val = value.val / 10000000000 := by
      norm_num [div_uintOfNat_val value hDivisorLt (by norm_num)]
    have hRec := log10SearchContract1_val
      (add r (uintOfNat 10)) (div value (uintOfNat 10000000000)) s
      (by rw [hAdd]; omega)
    simp only [log10SearchContract2, log10Search2, hBranch, if_true]
    simpa [hAdd, hDiv, hNatBranch, hNatBranchRaw] using hRec
  · have hValBranch : ¬ (uintOfNat (10 ^ 10 - 1)).val < value.val := by
      simpa using hBranch
    have hNatBranch : ¬ 9999999999 < value.val := by simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 10 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hRec := log10SearchContract1_val r value s (by omega)
    simp only [log10SearchContract2, log10Search2, hBranch, if_false]
    simpa [hNatBranch, hNatBranchRaw] using hRec

private theorem log10SearchContract3_val
    (r value : Uint256) (s : ContractState)
    (hRMax : r.val + 39 < Verity.Core.Uint256.modulus) :
    ((log10SearchContract3 r value).run s).fst.val =
      log10Search3 r.val value.val := by
  have hThresholdLt : 99999999999999999999 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hDivisorLt : 100000000000000000000 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hThresholdVal : (uintOfNat (10 ^ 20 - 1)).val =
      99999999999999999999 := by
    norm_num [uintOfNat_val_of_lt hThresholdLt]
  by_cases hBranch : uintOfNat (10 ^ 20 - 1) < value
  · have hNatBranch : 99999999999999999999 < value.val := by
      have hValBranch : (uintOfNat (10 ^ 20 - 1)).val < value.val := hBranch
      simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : 10 ^ 20 - 1 < value.val := by
      norm_num
      exact hNatBranch
    have hAdd : (add r (uintOfNat 20)).val = r.val + 20 :=
      add_small_val r (by omega)
    have hDiv :
        (div value (uintOfNat 100000000000000000000)).val =
          value.val / 100000000000000000000 := by
      norm_num [div_uintOfNat_val value hDivisorLt (by norm_num)]
    have hRec := log10SearchContract2_val
      (add r (uintOfNat 20)) (div value (uintOfNat 100000000000000000000)) s
      (by rw [hAdd]; omega)
    simp only [log10SearchContract3, log10Search3, hBranch, if_true]
    simpa [hAdd, hDiv, hNatBranch, hNatBranchRaw] using hRec
  · have hNatBranch : ¬ 99999999999999999999 < value.val := by
      have hValBranch : ¬ (uintOfNat (10 ^ 20 - 1)).val < value.val := by
        simpa using hBranch
      simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 20 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hRec := log10SearchContract2_val r value s (by omega)
    simp only [log10SearchContract3, log10Search3, hBranch, if_false]
    simpa [hNatBranch, hNatBranchRaw] using hRec

private theorem log10SearchContract4_val
    (r value : Uint256) (s : ContractState)
    (hRMax : r.val + 77 < Verity.Core.Uint256.modulus) :
    ((log10SearchContract4 r value).run s).fst.val =
      log10Search4 r.val value.val := by
  have hThresholdLt :
      99999999999999999999999999999999999999 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hDivisorLt :
      100000000000000000000000000000000000000 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hThresholdVal : (uintOfNat (10 ^ 38 - 1)).val =
      99999999999999999999999999999999999999 := by
    norm_num [uintOfNat_val_of_lt hThresholdLt]
  by_cases hBranch : uintOfNat (10 ^ 38 - 1) < value
  · have hNatBranch :
        99999999999999999999999999999999999999 < value.val := by
      have hValBranch : (uintOfNat (10 ^ 38 - 1)).val < value.val := hBranch
      simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : 10 ^ 38 - 1 < value.val := by
      norm_num
      exact hNatBranch
    have hAdd : (add r (uintOfNat 38)).val = r.val + 38 :=
      add_small_val r (by omega)
    have hDiv :
        (div value (uintOfNat 100000000000000000000000000000000000000)).val =
          value.val / 100000000000000000000000000000000000000 := by
      norm_num [div_uintOfNat_val value hDivisorLt (by norm_num)]
    have hRec := log10SearchContract3_val
      (add r (uintOfNat 38))
        (div value (uintOfNat 100000000000000000000000000000000000000)) s
      (by rw [hAdd]; omega)
    simp only [log10SearchContract4, log10Search4, hBranch, if_true]
    simpa [hAdd, hDiv, hNatBranch, hNatBranchRaw] using hRec
  · have hNatBranch :
        ¬ 99999999999999999999999999999999999999 < value.val := by
      have hValBranch : ¬ (uintOfNat (10 ^ 38 - 1)).val < value.val := by
        simpa using hBranch
      simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 38 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hRec := log10SearchContract3_val r value s (by omega)
    simp only [log10SearchContract4, log10Search4, hBranch, if_false]
    simpa [hNatBranch, hNatBranchRaw] using hRec

private theorem log10_run_eq_search (x : Uint256) (s : ContractState) :
    ((log10 x).run s).fst.val = log10Search4 0 x.val := by
  rw [log10, log10_eq_searchContract x]
  exact log10SearchContract4_val 0 x s (by
    rw [show (0 : Uint256).val = 0 by rfl]
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num)

private def log10ScaleLoopNat : List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], scale, exponent => (scale, exponent)
  | (decrement, multiplier) :: rest, scale, exponent =>
      if decrement - 1 < exponent then
        log10ScaleLoopNat rest (scale * multiplier) (exponent - decrement)
      else
        log10ScaleLoopNat rest scale exponent

private def log10ScaleLoopContract :
    List (Nat × Nat) → Uint256 → Uint256 → Contract (Uint256 × Uint256)
  | [], scale, exponent => Pure.pure (scale, exponent)
  | (decrement, multiplier) :: rest, scale, exponent =>
      if (uintOfNat (decrement - 1)) < exponent then
        log10ScaleLoopContract rest
          (mul scale (uintOfNat multiplier)) (sub exponent (uintOfNat decrement))
      else
        log10ScaleLoopContract rest scale exponent

private theorem log10ScaleLoopContract_success
    (chunks : List (Nat × Nat)) (scale exponent : Uint256) (s : ContractState) :
    (log10ScaleLoopContract chunks scale exponent).run s =
      ContractResult.success
        ((log10ScaleLoopContract chunks scale exponent).run s).fst s := by
  induction chunks generalizing scale exponent with
  | nil =>
      simp [log10ScaleLoopContract, Contract.run, Pure.pure, Verity.pure,
        ContractResult.fst]
  | cons chunk rest ih =>
      unfold log10ScaleLoopContract
      by_cases hBranch : uintOfNat (chunk.1 - 1) < exponent
      · simp [hBranch]
        exact ih (mul scale (uintOfNat chunk.2)) (sub exponent (uintOfNat chunk.1))
      · simp [hBranch]
        exact ih scale exponent

private theorem log10ScaleLoopContract_val
    (chunks : List (Nat × Nat)) (scale exponent : Uint256) (s : ContractState)
    (hChunks : ∀ c ∈ chunks, c.2 = 10 ^ c.1)
    (hDecPos : ∀ c ∈ chunks, 0 < c.1)
    (hDecLe : ∀ c ∈ chunks, c.1 ≤ 38)
    (hInv : scale.val * 10 ^ exponent.val < Verity.Core.Uint256.modulus)
    (hExpLe : exponent.val ≤ 77) :
    let outNat := log10ScaleLoopNat chunks scale.val exponent.val
    ((log10ScaleLoopContract chunks scale exponent).run s).fst.1.val = outNat.1 ∧
      ((log10ScaleLoopContract chunks scale exponent).run s).fst.2.val = outNat.2 := by
  induction chunks generalizing scale exponent with
  | nil =>
      simp [log10ScaleLoopContract, log10ScaleLoopNat, Contract.run, Pure.pure,
        Verity.pure]
  | cons chunk rest ih =>
      have hMultEq : chunk.2 = 10 ^ chunk.1 := hChunks chunk (by simp)
      have hDecLeHead : chunk.1 ≤ 38 := hDecLe chunk (by simp)
      have hRestChunks : ∀ c ∈ rest, c.2 = 10 ^ c.1 := by
        intro c hc
        exact hChunks c (by simp [hc])
      have hRestDecPos : ∀ c ∈ rest, 0 < c.1 := by
        intro c hc
        exact hDecPos c (by simp [hc])
      have hRestDecLe : ∀ c ∈ rest, c.1 ≤ 38 := by
        intro c hc
        exact hDecLe c (by simp [hc])
      have hThresholdLt : chunk.1 - 1 < Verity.Core.Uint256.modulus := by
        rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
        omega
      by_cases hBranch : uintOfNat (chunk.1 - 1) < exponent
      · have hNatBranch : chunk.1 - 1 < exponent.val := by
          have hValBranch : (uintOfNat (chunk.1 - 1)).val < exponent.val := hBranch
          simpa [uintOfNat_val_of_lt hThresholdLt] using hValBranch
        have hDecLeExp : chunk.1 ≤ exponent.val := by omega
        have hMulLt : scale.val * chunk.2 < Verity.Core.Uint256.modulus := by
          rw [hMultEq]
          have hPowLe : 10 ^ chunk.1 ≤ 10 ^ exponent.val :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 10) hDecLeExp
          exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hPowLe) hInv
        have hMultLtMod : chunk.2 < Verity.Core.Uint256.modulus := by
          rw [hMultEq]
          rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
          have hPowLe : 10 ^ chunk.1 ≤ 10 ^ 38 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 10) hDecLeHead
          have hPowLt : 10 ^ 38 < 2 ^ 256 := by norm_num
          omega
        have hMulVal : (mul scale (uintOfNat chunk.2)).val = scale.val * chunk.2 :=
          mul_small_val scale hMultLtMod hMulLt
        have hSubVal :
            (sub exponent (uintOfNat chunk.1)).val = exponent.val - chunk.1 :=
          sub_small_val exponent hDecLeExp
        have hInvRec :
            (mul scale (uintOfNat chunk.2)).val *
              10 ^ (sub exponent (uintOfNat chunk.1)).val <
                Verity.Core.Uint256.modulus := by
          rw [hMulVal, hSubVal, hMultEq]
          have hExp : chunk.1 + (exponent.val - chunk.1) = exponent.val := by omega
          rw [Nat.mul_assoc, ← Nat.pow_add, hExp]
          exact hInv
        have hExpLeRec : (sub exponent (uintOfNat chunk.1)).val ≤ 77 := by
          rw [hSubVal]
          omega
        simp only [log10ScaleLoopContract, log10ScaleLoopNat, hBranch,
          hNatBranch, if_true]
        have hRec := ih (mul scale (uintOfNat chunk.2))
          (sub exponent (uintOfNat chunk.1)) hRestChunks hRestDecPos hRestDecLe
          hInvRec hExpLeRec
        simpa [hMulVal, hSubVal] using hRec
      · have hNatBranch : ¬ chunk.1 - 1 < exponent.val := by
          have hValBranch : ¬ (uintOfNat (chunk.1 - 1)).val < exponent.val := by
            simpa using hBranch
          simpa [uintOfNat_val_of_lt hThresholdLt] using hValBranch
        simp only [log10ScaleLoopContract, log10ScaleLoopNat, hBranch,
          hNatBranch, if_false]
        exact ih scale exponent hRestChunks hRestDecPos hRestDecLe hInv hExpLe

private def log10ScaleChunks : List (Nat × Nat) :=
  [(38, 10 ^ 38), (20, 10 ^ 20), (10, 10 ^ 10), (5, 10 ^ 5),
    (4, 10 ^ 4), (2, 10 ^ 2)]

private theorem log10ScaleChunks_spec :
    (∀ c ∈ log10ScaleChunks, c.2 = 10 ^ c.1) ∧
      (∀ c ∈ log10ScaleChunks, 0 < c.1) ∧
      (∀ c ∈ log10ScaleChunks, c.1 ≤ 38) := by
  constructor
  · intro c hc
    simp [log10ScaleChunks] at hc
    rcases hc with hc | hc | hc | hc | hc | hc <;> subst c <;> norm_num
  constructor
  · intro c hc
    simp [log10ScaleChunks] at hc
    rcases hc with hc | hc | hc | hc | hc | hc <;> subst c <;> norm_num
  · intro c hc
    simp [log10ScaleChunks] at hc
    rcases hc with hc | hc | hc | hc | hc | hc <;> subst c <;> norm_num

private def log10ScaleNat (exponent : Nat) : Nat :=
  let out := log10ScaleLoopNat log10ScaleChunks 1 exponent
  if 0 < out.2 then out.1 * 10 else out.1

private def log10ScaleFinalLoopContract :
    List (Nat × Nat) → Uint256 → Uint256 → Contract Uint256
  | [], scale, exponent =>
      if (uintOfNat 0) < exponent then
        Pure.pure (mul scale (uintOfNat 10))
      else
        Pure.pure scale
  | (decrement, multiplier) :: rest, scale, exponent =>
      if (uintOfNat (decrement - 1)) < exponent then
        log10ScaleFinalLoopContract rest
          (mul scale (uintOfNat multiplier)) (sub exponent (uintOfNat decrement))
      else
        log10ScaleFinalLoopContract rest scale exponent

private def log10ScaleFinalLoopThenContract :
    List (Nat × Nat) → Uint256 → Uint256 → (Uint256 → Contract Uint256) → Contract Uint256
  | [], scale, exponent, k =>
      if (uintOfNat 0) < exponent then
        k (mul scale (uintOfNat 10))
      else
        k scale
  | (decrement, multiplier) :: rest, scale, exponent, k =>
      if (uintOfNat (decrement - 1)) < exponent then
        log10ScaleFinalLoopThenContract rest
          (mul scale (uintOfNat multiplier)) (sub exponent (uintOfNat decrement)) k
      else
        log10ScaleFinalLoopThenContract rest scale exponent k

private def log10ScaleContract (r : Uint256) : Contract Uint256 := do
  let mut scale := uintOfNat 1
  let mut exponent := r
  if (uintOfNat 37) < exponent then
    scale := mul scale (uintOfNat (10 ^ 38))
    exponent := sub exponent (uintOfNat 38)
  else
    Pure.pure ()
  if (uintOfNat 19) < exponent then
    scale := mul scale (uintOfNat (10 ^ 20))
    exponent := sub exponent (uintOfNat 20)
  else
    Pure.pure ()
  if (uintOfNat 9) < exponent then
    scale := mul scale (uintOfNat (10 ^ 10))
    exponent := sub exponent (uintOfNat 10)
  else
    Pure.pure ()
  if (uintOfNat 4) < exponent then
    scale := mul scale (uintOfNat (10 ^ 5))
    exponent := sub exponent (uintOfNat 5)
  else
    Pure.pure ()
  if (uintOfNat 3) < exponent then
    scale := mul scale (uintOfNat (10 ^ 4))
    exponent := sub exponent (uintOfNat 4)
  else
    Pure.pure ()
  if (uintOfNat 1) < exponent then
    scale := mul scale (uintOfNat (10 ^ 2))
    exponent := sub exponent (uintOfNat 2)
  else
    Pure.pure ()
  if (uintOfNat 0) < exponent then
    Pure.pure (mul scale (uintOfNat 10))
  else
    Pure.pure scale

private theorem log10ScaleFinalLoopContract_success
    (chunks : List (Nat × Nat)) (scale exponent : Uint256) (s : ContractState) :
    (log10ScaleFinalLoopContract chunks scale exponent).run s =
      ContractResult.success
        ((log10ScaleFinalLoopContract chunks scale exponent).run s).fst s := by
  induction chunks generalizing scale exponent with
  | nil =>
      unfold log10ScaleFinalLoopContract
      by_cases hBranch : uintOfNat 0 < exponent
      · simp [hBranch, Contract.run, Pure.pure, Verity.pure, ContractResult.fst]
      · simp [hBranch, Contract.run, Pure.pure, Verity.pure, ContractResult.fst]
  | cons chunk rest ih =>
      unfold log10ScaleFinalLoopContract
      by_cases hBranch : uintOfNat (chunk.1 - 1) < exponent
      · simp [hBranch]
        exact ih (mul scale (uintOfNat chunk.2)) (sub exponent (uintOfNat chunk.1))
      · simp [hBranch]
        exact ih scale exponent

private theorem log10ScaleFinalLoopContract_val
    (chunks : List (Nat × Nat)) (scale exponent : Uint256) (s : ContractState)
    (hChunks : ∀ c ∈ chunks, c.2 = 10 ^ c.1)
    (hDecPos : ∀ c ∈ chunks, 0 < c.1)
    (hDecLe : ∀ c ∈ chunks, c.1 ≤ 38)
    (hInv : scale.val * 10 ^ exponent.val < Verity.Core.Uint256.modulus)
    (hExpLe : exponent.val ≤ 77) :
    let outNat := log10ScaleLoopNat chunks scale.val exponent.val
    ((log10ScaleFinalLoopContract chunks scale exponent).run s).fst.val =
      if 0 < outNat.2 then outNat.1 * 10 else outNat.1 := by
  induction chunks generalizing scale exponent with
  | nil =>
      have hZeroVal : (uintOfNat 0).val = 0 := by
        rw [uintOfNat_val_of_lt]
        rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
        norm_num
      unfold log10ScaleFinalLoopContract log10ScaleLoopNat
      by_cases hBranch : uintOfNat 0 < exponent
      · have hNatBranch : 0 < exponent.val := by
          have hValBranch : (uintOfNat 0).val < exponent.val := hBranch
          simpa [hZeroVal] using hValBranch
        have hTenLt : 10 < Verity.Core.Uint256.modulus := by
          rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
          norm_num
        have hMulLt : scale.val * 10 < Verity.Core.Uint256.modulus := by
          have hPowLe : 10 ≤ 10 ^ exponent.val := by
            have hOneLe : 1 ≤ exponent.val := hNatBranch
            exact Nat.le_trans (by norm_num : 10 ≤ 10 ^ 1)
              (Nat.pow_le_pow_right (by decide : 1 ≤ 10) hOneLe)
          exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hPowLe) hInv
        have hMulVal : (mul scale (uintOfNat 10)).val = scale.val * 10 :=
          mul_small_val scale hTenLt hMulLt
        simp [hBranch, hNatBranch, Contract.run, Pure.pure, Verity.pure, hMulVal]
      · have hNatBranch : ¬ 0 < exponent.val := by
          intro h
          apply hBranch
          simpa [hZeroVal] using h
        simp [hBranch, hNatBranch, Contract.run, Pure.pure, Verity.pure]
  | cons chunk rest ih =>
      have hMultEq : chunk.2 = 10 ^ chunk.1 := hChunks chunk (by simp)
      have hDecLeHead : chunk.1 ≤ 38 := hDecLe chunk (by simp)
      have hRestChunks : ∀ c ∈ rest, c.2 = 10 ^ c.1 := by
        intro c hc
        exact hChunks c (by simp [hc])
      have hRestDecPos : ∀ c ∈ rest, 0 < c.1 := by
        intro c hc
        exact hDecPos c (by simp [hc])
      have hRestDecLe : ∀ c ∈ rest, c.1 ≤ 38 := by
        intro c hc
        exact hDecLe c (by simp [hc])
      have hThresholdLt : chunk.1 - 1 < Verity.Core.Uint256.modulus := by
        rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
        omega
      by_cases hBranch : uintOfNat (chunk.1 - 1) < exponent
      · have hNatBranch : chunk.1 - 1 < exponent.val := by
          have hValBranch : (uintOfNat (chunk.1 - 1)).val < exponent.val := hBranch
          simpa [uintOfNat_val_of_lt hThresholdLt] using hValBranch
        have hDecLeExp : chunk.1 ≤ exponent.val := by omega
        have hMulLt : scale.val * chunk.2 < Verity.Core.Uint256.modulus := by
          rw [hMultEq]
          have hPowLe : 10 ^ chunk.1 ≤ 10 ^ exponent.val :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 10) hDecLeExp
          exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hPowLe) hInv
        have hMultLtMod : chunk.2 < Verity.Core.Uint256.modulus := by
          rw [hMultEq]
          rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
          have hPowLe : 10 ^ chunk.1 ≤ 10 ^ 38 :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 10) hDecLeHead
          have hPowLt : 10 ^ 38 < 2 ^ 256 := by norm_num
          omega
        have hMulVal : (mul scale (uintOfNat chunk.2)).val = scale.val * chunk.2 :=
          mul_small_val scale hMultLtMod hMulLt
        have hSubVal :
            (sub exponent (uintOfNat chunk.1)).val = exponent.val - chunk.1 :=
          sub_small_val exponent hDecLeExp
        have hInvRec :
            (mul scale (uintOfNat chunk.2)).val *
              10 ^ (sub exponent (uintOfNat chunk.1)).val <
                Verity.Core.Uint256.modulus := by
          rw [hMulVal, hSubVal, hMultEq]
          have hExp : chunk.1 + (exponent.val - chunk.1) = exponent.val := by omega
          rw [Nat.mul_assoc, ← Nat.pow_add, hExp]
          exact hInv
        have hExpLeRec : (sub exponent (uintOfNat chunk.1)).val ≤ 77 := by
          rw [hSubVal]
          omega
        simp only [log10ScaleFinalLoopContract, log10ScaleLoopNat, hBranch,
          hNatBranch, if_true]
        have hRec := ih (mul scale (uintOfNat chunk.2))
          (sub exponent (uintOfNat chunk.1)) hRestChunks hRestDecPos hRestDecLe
          hInvRec hExpLeRec
        simpa [hMulVal, hSubVal] using hRec
      · have hNatBranch : ¬ chunk.1 - 1 < exponent.val := by
          have hValBranch : ¬ (uintOfNat (chunk.1 - 1)).val < exponent.val := by
            simpa using hBranch
          simpa [uintOfNat_val_of_lt hThresholdLt] using hValBranch
        simp only [log10ScaleFinalLoopContract, log10ScaleLoopNat, hBranch,
          hNatBranch, if_false]
        exact ih scale exponent hRestChunks hRestDecPos hRestDecLe hInv hExpLe

private theorem log10ScaleContract_eq_finalLoop (r : Uint256) :
    log10ScaleContract r =
      log10ScaleFinalLoopContract log10ScaleChunks (uintOfNat 1) r := by
  simp [log10ScaleContract, log10ScaleFinalLoopContract, log10ScaleChunks,
    uintOfNat, Bind.bind, Pure.pure]

private theorem log10ScaleLoopNat_invariant
    (chunks : List (Nat × Nat)) (scale exponent : Nat)
    (hChunks : ∀ c ∈ chunks, c.2 = 10 ^ c.1) :
    let out := log10ScaleLoopNat chunks scale exponent
    out.1 * 10 ^ out.2 = scale * 10 ^ exponent := by
  induction chunks generalizing scale exponent with
  | nil =>
      simp [log10ScaleLoopNat]
  | cons chunk rest ih =>
      simp [log10ScaleLoopNat]
      by_cases hBranch : chunk.1 - 1 < exponent
      · simp [hBranch]
        have hMult : chunk.2 = 10 ^ chunk.1 := hChunks chunk (by simp)
        have hRest : ∀ c ∈ rest, c.2 = 10 ^ c.1 := by
          intro c hc
          exact hChunks c (by simp [hc])
        have hExp : chunk.1 + (exponent - chunk.1) = exponent := by
          by_cases hZero : chunk.1 = 0
          · omega
          · omega
        have h := ih (scale * chunk.2) (exponent - chunk.1) hRest
        simp only at h
        rw [h, hMult, Nat.mul_assoc, ← Nat.pow_add, hExp]
      · simp [hBranch]
        have hRest : ∀ c ∈ rest, c.2 = 10 ^ c.1 := by
          intro c hc
          exact hChunks c (by simp [hc])
        exact ih scale exponent hRest

private theorem log10ScaleLoopNat_exp_le_one (exponent : Nat) (hExp : exponent ≤ 77) :
    (log10ScaleLoopNat log10ScaleChunks 1 exponent).2 ≤ 1 := by
  simp [log10ScaleChunks, log10ScaleLoopNat]
  split_ifs <;> omega

private theorem log10ScaleNat_eq_pow (exponent : Nat) (hExp : exponent ≤ 77) :
    log10ScaleNat exponent = 10 ^ exponent := by
  unfold log10ScaleNat
  have hInv :
      (log10ScaleLoopNat log10ScaleChunks 1 exponent).1 *
        10 ^ (log10ScaleLoopNat log10ScaleChunks 1 exponent).2 = 10 ^ exponent := by
    have h := log10ScaleLoopNat_invariant log10ScaleChunks 1 exponent
      log10ScaleChunks_spec.1
    simpa [Nat.one_mul] using h
  have hOutLe :
      (log10ScaleLoopNat log10ScaleChunks 1 exponent).2 ≤ 1 :=
    log10ScaleLoopNat_exp_le_one exponent hExp
  set out := log10ScaleLoopNat log10ScaleChunks 1 exponent with hOut
  change (if 0 < out.2 then out.1 * 10 else out.1) = 10 ^ exponent
  by_cases hPos : 0 < out.2
  · have hOne : out.2 = 1 := by omega
    simp [hOne] at hInv ⊢
    exact hInv
  · have hZero : out.2 = 0 := by omega
    simp [hZero] at hInv ⊢
    exact hInv

private theorem log10ScaleContract_val (r : Uint256) (s : ContractState)
    (hR : r.val ≤ 77) :
    ((log10ScaleContract r).run s).fst.val = 10 ^ r.val := by
  rw [log10ScaleContract_eq_finalLoop]
  have hOneLt : 1 < Verity.Core.Uint256.modulus := by
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    norm_num
  have hOneVal : (uintOfNat 1).val = 1 := uintOfNat_val_of_lt hOneLt
  have hInv : (uintOfNat 1).val * 10 ^ r.val < Verity.Core.Uint256.modulus := by
    rw [hOneVal]
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    have hPowLe : 10 ^ r.val ≤ 10 ^ 77 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 10) hR
    have hPowLt : 10 ^ 77 < 2 ^ 256 := by norm_num
    omega
  have hFinal := log10ScaleFinalLoopContract_val log10ScaleChunks (uintOfNat 1) r s
    log10ScaleChunks_spec.1 log10ScaleChunks_spec.2.1 log10ScaleChunks_spec.2.2
    hInv hR
  have hScaleNat : log10ScaleNat r.val = 10 ^ r.val :=
    log10ScaleNat_eq_pow r.val hR
  simpa [log10ScaleNat, hOneVal] using hFinal.trans hScaleNat

private theorem log10ScaleContract_success (r : Uint256) (s : ContractState) :
    (log10ScaleContract r).run s =
      ContractResult.success ((log10ScaleContract r).run s).fst s := by
  rw [log10ScaleContract_eq_finalLoop]
  exact log10ScaleFinalLoopContract_success log10ScaleChunks (uintOfNat 1) r s

private theorem log10ScaleFinalLoopThenContract_eq_bind
    (chunks : List (Nat × Nat)) (scale exponent : Uint256)
    (k : Uint256 → Contract Uint256) :
    log10ScaleFinalLoopThenContract chunks scale exponent k =
      (do
        let scale ← log10ScaleFinalLoopContract chunks scale exponent
        k scale) := by
  induction chunks generalizing scale exponent with
  | nil =>
      unfold log10ScaleFinalLoopThenContract log10ScaleFinalLoopContract
      by_cases hBranch : uintOfNat 0 < exponent
      · simp [hBranch, Bind.bind, Pure.pure]
      · simp [hBranch, Bind.bind, Pure.pure]
  | cons chunk rest ih =>
      unfold log10ScaleFinalLoopThenContract log10ScaleFinalLoopContract
      by_cases hBranch : uintOfNat (chunk.1 - 1) < exponent
      · simp [hBranch]
        exact ih (mul scale (uintOfNat chunk.2)) (sub exponent (uintOfNat chunk.1))
      · simp [hBranch]
        exact ih scale exponent

private def log10UpSearchFrom (x floor : Nat) : Nat :=
  if 10 ^ floor < x then floor + 1 else floor

private def log10UpSearch (x : Nat) : Nat :=
  log10UpSearchFrom x (log10Search4 0 x)

private def log10UpRoundContract (x r : Uint256) : Contract Uint256 := do
  let scale ← log10ScaleContract r
  if scale < x then
    Pure.pure (add r (uintOfNat 1))
  else
    Pure.pure r

private def log10UpRoundInlineContract (x r : Uint256) : Contract Uint256 := do
  let mut scale := 1
  let mut exponent := r
  if 37 < exponent then
    scale := mul scale 100000000000000000000000000000000000000
    exponent := sub exponent 38
  else
    Pure.pure ()
  if 19 < exponent then
    scale := mul scale 100000000000000000000
    exponent := sub exponent 20
  else
    Pure.pure ()
  if 9 < exponent then
    scale := mul scale 10000000000
    exponent := sub exponent 10
  else
    Pure.pure ()
  if 4 < exponent then
    scale := mul scale 100000
    exponent := sub exponent 5
  else
    Pure.pure ()
  if 3 < exponent then
    scale := mul scale 10000
    exponent := sub exponent 4
  else
    Pure.pure ()
  if 1 < exponent then
    scale := mul scale 100
    exponent := sub exponent 2
  else
    Pure.pure ()
  if 0 < exponent then
    scale := mul scale 10
  else
    Pure.pure ()
  if scale < x then
    Pure.pure (add r 1)
  else
    Pure.pure r

private theorem log10UpRoundContract_val (x r : Uint256) (s : ContractState)
    (hR : r.val ≤ 77) :
    ((log10UpRoundContract x r).run s).fst.val =
      if 10 ^ r.val < x.val then r.val + 1 else r.val := by
  have hScaleVal := log10ScaleContract_val r s hR
  have hScaleSuccess := log10ScaleContract_success r s
  have hScaleSuccessRaw :
      log10ScaleContract r s =
        ContractResult.success ((log10ScaleContract r).run s).fst s :=
    Contract.eq_of_run_success hScaleSuccess
  have hAdd : (add r (uintOfNat 1)).val = r.val + 1 := by
    apply add_small_val
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 by rfl]
    omega
  change (Contract.run
      (Verity.bind (log10ScaleContract r)
        (fun scale =>
          if scale < x then Pure.pure (add r (uintOfNat 1)) else Pure.pure r)) s).fst.val =
    (if 10 ^ r.val < x.val then r.val + 1 else r.val)
  unfold Contract.run Verity.bind
  rw [hScaleSuccessRaw]
  by_cases hBranch : ((log10ScaleContract r).run s).fst < x
  · have hNatBranch : 10 ^ r.val < x.val := by
      have hValBranch : ((log10ScaleContract r).run s).fst.val < x.val := hBranch
      simpa [hScaleVal] using hValBranch
    simp [hBranch, hNatBranch, Pure.pure, Verity.pure, hAdd]
  · have hNatBranch : ¬ 10 ^ r.val < x.val := by
      intro hNat
      apply hBranch
      simpa [hScaleVal] using hNat
    simp [hBranch, hNatBranch, Pure.pure, Verity.pure]

private theorem log10UpRoundContract_success
    (x r : Uint256) (s : ContractState) :
    (log10UpRoundContract x r).run s =
      ContractResult.success ((log10UpRoundContract x r).run s).fst s := by
  have hScaleSuccess := log10ScaleContract_success r s
  have hScaleSuccessRaw :
      log10ScaleContract r s =
        ContractResult.success ((log10ScaleContract r).run s).fst s :=
    Contract.eq_of_run_success hScaleSuccess
  change (Contract.run
      (Verity.bind (log10ScaleContract r)
        (fun scale =>
          if scale < x then Pure.pure (add r (uintOfNat 1)) else Pure.pure r)) s) =
    ContractResult.success
      ((Contract.run
        (Verity.bind (log10ScaleContract r)
          (fun scale =>
            if scale < x then Pure.pure (add r (uintOfNat 1)) else Pure.pure r)) s).fst) s
  unfold Contract.run Verity.bind
  rw [hScaleSuccessRaw]
  by_cases hBranch : ((log10ScaleContract r).run s).fst < x
  · simp only [hBranch, if_true, Pure.pure, Verity.pure, ContractResult.fst_success]
  · simp only [hBranch, if_false, Pure.pure, Verity.pure, ContractResult.fst_success]

private theorem log10UpRoundInline_eq_roundContract (x r : Uint256) :
    log10UpRoundInlineContract x r = log10UpRoundContract x r := by
  have hInline :
      log10UpRoundInlineContract x r =
        log10ScaleFinalLoopThenContract log10ScaleChunks (uintOfNat 1) r
          (fun scale =>
            if scale < x then Pure.pure (add r (uintOfNat 1)) else Pure.pure r) := by
    unfold log10UpRoundInlineContract log10ScaleFinalLoopThenContract log10ScaleChunks
    rfl
  rw [hInline, log10ScaleFinalLoopThenContract_eq_bind]
  rw [← log10ScaleContract_eq_finalLoop r]
  rfl

private theorem log10UpRoundInlineContract_val (x r : Uint256) (s : ContractState)
    (hR : r.val ≤ 77) :
    ((log10UpRoundInlineContract x r).run s).fst.val =
      if 10 ^ r.val < x.val then r.val + 1 else r.val := by
  rw [log10UpRoundInline_eq_roundContract]
  exact log10UpRoundContract_val x r s hR

private theorem log10Up_eq_log10_roundInline (x : Uint256) :
    Tamago.Utils.FixedPointMathLibBase.log10Up x =
      (do
        let r ← Tamago.Utils.FixedPointMathLibBase.log10 x
        log10UpRoundInlineContract x r) := by
  unfold Tamago.Utils.FixedPointMathLibBase.log10Up log10UpRoundInlineContract
  rfl

private theorem log10Search_initial_le_77 (x : Uint256) :
    log10Search4 0 x.val ≤ 77 := by
  have hxLt10 : x.val < 10 ^ 78 := by
    have hxLt2 : x.val < 2 ^ 256 := by
      simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
    have hPow : 2 ^ 256 < 10 ^ 78 := by norm_num
    omega
  by_cases hZero : x.val = 0
  · rw [hZero]
    norm_num [log10Search4, log10Search3, log10Search2, log10Search1,
      log10Search0, log10Final]
  · have hBounds := log10Search_initial_bounds x.val hxLt10
    have hPowLt : 10 ^ log10Search4 0 x.val < 10 ^ 78 :=
      lt_of_le_of_lt (hBounds.1 hZero) hxLt10
    have hExpLt : log10Search4 0 x.val < 78 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).1 hPowLt
    omega

private theorem log10Up_run_eq_search (x : Uint256) (s : ContractState) :
    ((log10Up x).run s).fst.val = log10UpSearch x.val := by
  rw [log10Up, log10Up_eq_log10_roundInline x]
  have hLogSuccess := log10SearchContract4_success 0 x s
  have hLogSuccessRaw :
      (Tamago.Utils.FixedPointMathLibBase.log10 x).run s =
        ContractResult.success ((Tamago.Utils.FixedPointMathLibBase.log10 x).run s).fst s := by
    rw [log10_eq_searchContract x]
    exact hLogSuccess
  have hLogSuccessRaw' :
      Tamago.Utils.FixedPointMathLibBase.log10 x s =
        ContractResult.success ((Tamago.Utils.FixedPointMathLibBase.log10 x).run s).fst s :=
    Contract.eq_of_run_success hLogSuccessRaw
  change (Contract.run
      (Verity.bind (Tamago.Utils.FixedPointMathLibBase.log10 x)
        (fun r => log10UpRoundInlineContract x r)) s).fst.val =
    log10UpSearch x.val
  unfold Contract.run Verity.bind
  rw [hLogSuccessRaw']
  have hRound := log10UpRoundInlineContract_val x
    ((Tamago.Utils.FixedPointMathLibBase.log10 x).run s).fst s
    (by rw [log10_run_eq_search x s]; exact log10Search_initial_le_77 x)
  have hLogEq := log10_run_eq_search x s
  simpa [log10UpSearch, log10UpSearchFrom, hLogEq] using hRound

private theorem log_floor_returns_math_floor
    (base : Nat) (hBase : 1 < base) (x result : Uint256)
    (hEq : result.val = Nat.log base x.val) :
    logFloor_property base x result := by
  unfold logFloor_property
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    apply Verity.Core.Uint256.ext
    rw [hEq, hZero]
    simp
  · intro hNonzero
    rw [hEq]
    exact Nat.pow_log_le_self base hNonzero
  · rw [hEq]
    exact Nat.lt_pow_succ_log_self hBase x.val

private theorem log_up_returns_math_ceil
    (base : Nat) (hBase : 1 < base) (x result : Uint256)
    (hEq : result.val = Nat.clog base x.val) :
    logUp_property base x result := by
  unfold logUp_property
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    apply Verity.Core.Uint256.ext
    rw [hEq]
    have hClog : Nat.clog base x.val = 0 := by
      exact Nat.clog_of_right_le_one (n := x.val) (by omega) base
    rw [hClog]
    rfl
  · rw [hEq]
    exact Nat.le_pow_clog hBase x.val
  · intro hGtOne
    rw [hEq]
    exact Nat.pow_pred_clog_lt_self hBase hGtOne

theorem log2_returns_math_floor (x : Uint256) (s : ContractState) :
    logFloor_property 2 x ((log2 x).run s).fst := by
  unfold logFloor_property
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hBounds := log2Search_initial_bounds x.val hxLt
  have hEq := log2_run_eq_search x s
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    apply Verity.Core.Uint256.ext
    rw [hEq, hZero]
    norm_num [log2Search]
  · intro hNonzero
    rw [hEq]
    exact hBounds.1 hNonzero
  · rw [hEq]
    exact hBounds.2

theorem log2Up_returns_math_ceil (x : Uint256) (s : ContractState) :
    logUp_property 2 x ((log2Up x).run s).fst := by
  unfold logUp_property
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hBounds := log2Search_initial_bounds x.val hxLt
  have hEq := log2Up_run_eq_search x s
  let floor := log2Search 7 0 x.val
  have hFloorDef : floor = log2Search 7 0 x.val := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    apply Verity.Core.Uint256.ext
    rw [hEq, hZero]
    norm_num [log2UpSearch, log2Search]
  · rw [hEq, log2UpSearch]
    by_cases hRound : 2 ^ log2Search 7 0 x.val < x.val
    · simp [hRound]
      exact Nat.le_of_lt hBounds.2
    · simp [hRound]
      exact Nat.le_of_not_gt hRound
  · intro hxGt
    rw [hEq, log2UpSearch]
    by_cases hRound : 2 ^ log2Search 7 0 x.val < x.val
    · simp [hRound]
    · simp [hRound]
      by_cases hFloorZero : log2Search 7 0 x.val = 0
      · simp [hFloorZero]
        exact hxGt
      · have hFloorPos : 0 < log2Search 7 0 x.val := Nat.pos_of_ne_zero hFloorZero
        have hPredLt :
            2 ^ (log2Search 7 0 x.val - 1) < 2 ^ log2Search 7 0 x.val := by
          exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.sub_one_lt hFloorZero)
        have hxNonzero : x.val ≠ 0 := by omega
        exact lt_of_lt_of_le hPredLt (hBounds.1 hxNonzero)

theorem log10_returns_math_floor (x : Uint256) (s : ContractState) :
    logFloor_property 10 x ((log10 x).run s).fst := by
  unfold logFloor_property
  have hxLt2 : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hxLt10 : x.val < 10 ^ 78 := by
    have hPow : 2 ^ 256 < 10 ^ 78 := by norm_num
    omega
  have hBounds := log10Search_initial_bounds x.val hxLt10
  have hEq := log10_run_eq_search x s
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    apply Verity.Core.Uint256.ext
    rw [hEq, hZero]
    norm_num [log10Search4, log10Search3, log10Search2, log10Search1,
      log10Search0, log10Final]
  · intro hNonzero
    rw [hEq]
    exact hBounds.1 hNonzero
  · rw [hEq]
    exact hBounds.2

theorem log10Up_returns_math_ceil (x : Uint256) (s : ContractState) :
    logUp_property 10 x ((log10Up x).run s).fst := by
  unfold logUp_property
  have hxLt10 : x.val < 10 ^ 78 := by
    have hxLt2 : x.val < 2 ^ 256 := by
      simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
    have hPow : 2 ^ 256 < 10 ^ 78 := by norm_num
    omega
  have hBounds := log10Search_initial_bounds x.val hxLt10
  have hEq := log10Up_run_eq_search x s
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    apply Verity.Core.Uint256.ext
    rw [hEq, hZero]
    norm_num [log10UpSearch, log10UpSearchFrom, log10Search4, log10Search3, log10Search2,
      log10Search1, log10Search0, log10Final]
  · rw [hEq, log10UpSearch]
    by_cases hRound : 10 ^ log10Search4 0 x.val < x.val
    · simp [log10UpSearchFrom, hRound]
      exact Nat.le_of_lt hBounds.2
    · simp [log10UpSearchFrom, hRound]
      exact Nat.le_of_not_gt hRound
  · intro hxGt
    rw [hEq, log10UpSearch]
    by_cases hRound : 10 ^ log10Search4 0 x.val < x.val
    · simp [log10UpSearchFrom, hRound]
    · simp [log10UpSearchFrom, hRound]
      by_cases hFloorZero : log10Search4 0 x.val = 0
      · simp [hFloorZero]
        exact hxGt
      · have hPredLt :
            10 ^ (log10Search4 0 x.val - 1) < 10 ^ log10Search4 0 x.val := by
          exact Nat.pow_lt_pow_right (by decide : 1 < 10) (Nat.sub_one_lt hFloorZero)
        have hxNonzero : x.val ≠ 0 := by omega
        exact lt_of_lt_of_le hPredLt (hBounds.1 hxNonzero)

private theorem log256Base_run_success_fst (x : Uint256) (s : ContractState) :
    (Tamago.Utils.FixedPointMathLibBase.log256 x).run s =
      ContractResult.success
        ((Tamago.Utils.FixedPointMathLibBase.log256 x).run s).fst s := by
  simp [Tamago.Utils.FixedPointMathLibBase.log256, Contract.run,
    Bind.bind, Pure.pure, shr_val, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp [Verity.pure, ContractResult.fst]

private theorem log256_input_lt_next_power (x : Uint256) (s : ContractState) :
    x.val < 256 ^ (((log256 x).run s).fst.val + 1) := by
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  simp [log256, Tamago.Utils.FixedPointMathLibBase.log256, Contract.run,
    Bind.bind, Pure.pure, shr_val, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp_all [Verity.pure, ContractResult.fst] <;> omega

private theorem log256_power_le_input (x : Uint256) (s : ContractState) :
    x.val ≠ 0 → 256 ^ ((log256 x).run s).fst.val ≤ x.val := by
  intro hxNe
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  simp [log256, Tamago.Utils.FixedPointMathLibBase.log256, Contract.run,
    Bind.bind, Pure.pure, shr_val, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp_all [Verity.pure, ContractResult.fst] <;> omega

theorem log256_returns_math_floor (x : Uint256) (s : ContractState) :
    logFloor_property 256 x ((log256 x).run s).fst := by
  unfold logFloor_property
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
    subst x
    simp [log256, Tamago.Utils.FixedPointMathLibBase.log256, Contract.run,
      Bind.bind, Pure.pure, Verity.pure]
  · exact log256_power_le_input x s
  · exact log256_input_lt_next_power x s

private theorem log256Up_input_le_power (x : Uint256) (s : ContractState) :
    x.val ≤ 256 ^ ((log256Up x).run s).fst.val := by
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  simp [log256Up, Tamago.Utils.FixedPointMathLibBase.log256Up, Contract.run,
    Bind.bind, Pure.pure, shr_val, shl_val, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp_all [Verity.pure, ContractResult.fst] <;> omega

private theorem log256Up_prev_power_lt_input (x : Uint256) (s : ContractState) :
    1 < x.val → 256 ^ (((log256Up x).run s).fst.val - 1) < x.val := by
  intro hxGt
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  simp [log256Up, Tamago.Utils.FixedPointMathLibBase.log256Up, Contract.run,
    Bind.bind, Pure.pure, shr_val, shl_val, add, Verity.Core.Uint256.add,
    Verity.Core.Uint256.ofNat, OfNat.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp_all [Verity.pure, ContractResult.fst] <;> omega

theorem log256Up_returns_math_ceil (x : Uint256) (s : ContractState) :
    logUp_property 256 x ((log256Up x).run s).fst := by
  unfold logUp_property
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
    subst x
    simp [log256Up, Tamago.Utils.FixedPointMathLibBase.log256Up,
      Contract.run, Bind.bind, Pure.pure, Verity.pure]
  · exact log256Up_input_le_power x s
  · exact log256Up_prev_power_lt_input x s

theorem clamp_stays_within_bounds (x minValue maxValue : Uint256) (s : ContractState) :
    clamp_property x minValue maxValue ((clamp x minValue maxValue).run s).fst := by
  unfold clamp_property
  by_cases hBelow : x.val < minValue.val
  · have hMaxChoosesMin : ¬ minValue.val ≤ x.val := Nat.not_le_of_gt hBelow
    by_cases hInvalid : maxValue.val < minValue.val
    · have hMinAboveMax : ¬ minValue.val ≤ maxValue.val := Nat.not_le_of_gt hInvalid
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMaxChoosesMin, hMinAboveMax]
      · intro hValid
        exact False.elim (by omega)
      · intro hRange
        exact False.elim (by omega)
      · intro hLow
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMaxChoosesMin, hMinAboveMax]
    · have hValid : minValue.val ≤ maxValue.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        exact False.elim (hInvalid h)
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMaxChoosesMin, hValid]
      · intro hRange
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMaxChoosesMin, hValid]
      · intro hAbove
        exact False.elim (by omega)
  · have hMinLeX : minValue.val ≤ x.val := by omega
    by_cases hAbove : maxValue.val < x.val
    · have hXAboveMax : ¬ x.val ≤ maxValue.val := Nat.not_le_of_gt hAbove
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMinLeX, hXAboveMax]
      · intro hValid
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMinLeX, hXAboveMax]
        exact hValid
      · intro hRange
        exact False.elim (by omega)
      · intro hLow
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMinLeX, hXAboveMax]
    · have hXLeMax : x.val ≤ maxValue.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hInvalid
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMinLeX, hXLeMax]
      · intro _h
        simp [clamp, Contract.run, Verity.pure, Pure.pure, hMinLeX, hXLeMax]
      · intro hLow
        exact False.elim (by omega)
      · intro h
        exact False.elim (hAbove h)

-- tama: discharges=fixedPointMathLib_saturatingAdd_returns_exact_sum_when_no_overflow
theorem fixedPointMathLib_saturatingAdd_returns_exact_sum_when_no_overflow_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingAdd_returns_exact_sum_when_no_overflow
      x y ((saturatingAdd x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingAdd_returns_exact_sum_when_no_overflow,
    saturatingAdd_property] using
    (saturatingAdd_saturates_at_uint256_max x y s).1

-- tama: discharges=fixedPointMathLib_saturatingAdd_overflow_returns_max
theorem fixedPointMathLib_saturatingAdd_overflow_returns_max_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingAdd_overflow_returns_max
      x y ((saturatingAdd x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingAdd_overflow_returns_max, saturatingAdd_property] using
    (saturatingAdd_saturates_at_uint256_max x y s).2.1

-- tama: discharges=fixedPointMathLib_saturatingAdd_result_at_least_left_input
theorem fixedPointMathLib_saturatingAdd_result_at_least_left_input_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingAdd_result_at_least_left_input
      x y ((saturatingAdd x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingAdd_result_at_least_left_input,
    saturatingAdd_property] using
    (saturatingAdd_saturates_at_uint256_max x y s).2.2.1

-- tama: discharges=fixedPointMathLib_saturatingAdd_result_at_least_right_input
theorem fixedPointMathLib_saturatingAdd_result_at_least_right_input_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingAdd_result_at_least_right_input
      x y ((saturatingAdd x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingAdd_result_at_least_right_input,
    saturatingAdd_property] using
    (saturatingAdd_saturates_at_uint256_max x y s).2.2.2

-- tama: discharges=fixedPointMathLib_saturatingMul_returns_exact_product_when_no_overflow
theorem fixedPointMathLib_saturatingMul_returns_exact_product_when_no_overflow_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingMul_returns_exact_product_when_no_overflow
      x y ((saturatingMul x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingMul_returns_exact_product_when_no_overflow,
    saturatingMul_property] using
    (saturatingMul_saturates_at_uint256_max x y s).1

-- tama: discharges=fixedPointMathLib_saturatingMul_overflow_returns_max
theorem fixedPointMathLib_saturatingMul_overflow_returns_max_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingMul_overflow_returns_max
      x y ((saturatingMul x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingMul_overflow_returns_max, saturatingMul_property] using
    (saturatingMul_saturates_at_uint256_max x y s).2.1

-- tama: discharges=fixedPointMathLib_saturatingMul_left_zero_returns_zero
theorem fixedPointMathLib_saturatingMul_left_zero_returns_zero_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingMul_left_zero_returns_zero
      x y ((saturatingMul x y).run s).fst := by
  intro hZero
  exact (saturatingMul_saturates_at_uint256_max x y s).2.2 (Or.inl hZero)

-- tama: discharges=fixedPointMathLib_saturatingMul_right_zero_returns_zero
theorem fixedPointMathLib_saturatingMul_right_zero_returns_zero_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingMul_right_zero_returns_zero
      x y ((saturatingMul x y).run s).fst := by
  intro hZero
  exact (saturatingMul_saturates_at_uint256_max x y s).2.2 (Or.inr hZero)

-- tama: discharges=fixedPointMathLib_saturatingSub_subtrahend_at_least_input_returns_zero
theorem fixedPointMathLib_saturatingSub_subtrahend_at_least_input_returns_zero_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingSub_subtrahend_at_least_input_returns_zero
      x y ((saturatingSub x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingSub_subtrahend_at_least_input_returns_zero,
    saturatingSub_property] using
    (saturatingSub_never_underflows x y s).1

-- tama: discharges=fixedPointMathLib_saturatingSub_exact_when_input_at_least_subtrahend
theorem fixedPointMathLib_saturatingSub_exact_when_input_at_least_subtrahend_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingSub_exact_when_input_at_least_subtrahend
      x y ((saturatingSub x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingSub_exact_when_input_at_least_subtrahend,
    saturatingSub_property] using
    (saturatingSub_never_underflows x y s).2.1

-- tama: discharges=fixedPointMathLib_saturatingSub_result_at_most_input
theorem fixedPointMathLib_saturatingSub_result_at_most_input_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_saturatingSub_result_at_most_input
      x y ((saturatingSub x y).run s).fst := by
  simpa [fixedPointMathLib_saturatingSub_result_at_most_input, saturatingSub_property] using
    (saturatingSub_never_underflows x y s).2.2

-- tama: discharges=fixedPointMathLib_dist_spec
theorem fixedPointMathLib_dist_specs_hold (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_dist_spec x y ((dist x y).run s).fst := by
  simpa [fixedPointMathLib_dist_spec, dist_property] using
    dist_is_absolute_difference x y s

-- tama: discharges=fixedPointMathLib_avg_twice_result_le_sum
theorem fixedPointMathLib_avg_twice_result_le_sum_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_avg_twice_result_le_sum x y ((avg x y).run s).fst := by
  simpa [fixedPointMathLib_avg_twice_result_le_sum, avg_property] using
    (avg_returns_floor_average x y s).1

-- tama: discharges=fixedPointMathLib_avg_sum_lt_twice_next_result
theorem fixedPointMathLib_avg_sum_lt_twice_next_result_holds
    (x y : Uint256) (s : ContractState) :
    fixedPointMathLib_avg_sum_lt_twice_next_result x y ((avg x y).run s).fst := by
  simpa [fixedPointMathLib_avg_sum_lt_twice_next_result, avg_property] using
    (avg_returns_floor_average x y s).2

-- tama: discharges=fixedPointMathLib_sqrt_square_le_input
theorem fixedPointMathLib_sqrt_square_le_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_sqrt_square_le_input x ((sqrt x).run s).fst := by
  simpa [fixedPointMathLib_sqrt_square_le_input, sqrt_property] using
    (sqrt_returns_math_floor x s).1

-- tama: discharges=fixedPointMathLib_sqrt_input_lt_next_square
theorem fixedPointMathLib_sqrt_input_lt_next_square_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_sqrt_input_lt_next_square x ((sqrt x).run s).fst := by
  simpa [fixedPointMathLib_sqrt_input_lt_next_square, sqrt_property] using
    (sqrt_returns_math_floor x s).2

-- tama: discharges=fixedPointMathLib_cbrt_cube_le_input
theorem fixedPointMathLib_cbrt_cube_le_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_cbrt_cube_le_input x ((cbrt x).run s).fst := by
  simpa [fixedPointMathLib_cbrt_cube_le_input, cbrt_property] using
    (cbrt_returns_math_floor x s).1

-- tama: discharges=fixedPointMathLib_cbrt_input_lt_next_cube
theorem fixedPointMathLib_cbrt_input_lt_next_cube_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_cbrt_input_lt_next_cube x ((cbrt x).run s).fst := by
  simpa [fixedPointMathLib_cbrt_input_lt_next_cube, cbrt_property] using
    (cbrt_returns_math_floor x s).2

-- tama: discharges=fixedPointMathLib_log2_zero_returns_zero
theorem fixedPointMathLib_log2_zero_returns_zero_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log2_zero_returns_zero x ((log2 x).run s).fst := by
  intro hZero
  have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
  subst x
  apply Verity.Core.Uint256.ext
  simp [log2, Contract.run, Tamago.Utils.FixedPointMathLibBase.log2,
    Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=fixedPointMathLib_log2_power_le_input
theorem fixedPointMathLib_log2_power_le_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log2_power_le_input x ((log2 x).run s).fst := by
  simpa [fixedPointMathLib_log2_power_le_input, logFloor_property] using
    (log2_returns_math_floor x s).2.1

-- tama: discharges=fixedPointMathLib_log2_input_lt_next_power
theorem fixedPointMathLib_log2_input_lt_next_power_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log2_input_lt_next_power x ((log2 x).run s).fst := by
  simpa [fixedPointMathLib_log2_input_lt_next_power, logFloor_property] using
    (log2_returns_math_floor x s).2.2

-- tama: discharges=fixedPointMathLib_log2Up_zero_returns_zero
theorem fixedPointMathLib_log2Up_zero_returns_zero_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log2Up_zero_returns_zero x ((log2Up x).run s).fst := by
  intro hZero
  have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
  subst x
  apply Verity.Core.Uint256.ext
  simp [log2Up, Contract.run, Tamago.Utils.FixedPointMathLibBase.log2Up,
    Bind.bind, Verity.pure, Pure.pure, shl, Verity.Core.Uint256.shl,
    Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq]

-- tama: discharges=fixedPointMathLib_log2Up_input_le_power
theorem fixedPointMathLib_log2Up_input_le_power_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log2Up_input_le_power x ((log2Up x).run s).fst := by
  simpa [fixedPointMathLib_log2Up_input_le_power, logUp_property] using
    (log2Up_returns_math_ceil x s).2.1

-- tama: discharges=fixedPointMathLib_log2Up_prev_power_lt_input
theorem fixedPointMathLib_log2Up_prev_power_lt_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log2Up_prev_power_lt_input x ((log2Up x).run s).fst := by
  simpa [fixedPointMathLib_log2Up_prev_power_lt_input, logUp_property] using
    (log2Up_returns_math_ceil x s).2.2

-- tama: discharges=fixedPointMathLib_log10_zero_returns_zero
theorem fixedPointMathLib_log10_zero_returns_zero_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log10_zero_returns_zero x ((log10 x).run s).fst := by
  intro hZero
  have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
  subst x
  simp [log10, Contract.run, Tamago.Utils.FixedPointMathLibBase.log10, Bind.bind,
    Verity.pure, Pure.pure]

-- tama: discharges=fixedPointMathLib_log10_power_le_input
theorem fixedPointMathLib_log10_power_le_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log10_power_le_input x ((log10 x).run s).fst := by
  simpa [fixedPointMathLib_log10_power_le_input, logFloor_property] using
    (log10_returns_math_floor x s).2.1

-- tama: discharges=fixedPointMathLib_log10_input_lt_next_power
theorem fixedPointMathLib_log10_input_lt_next_power_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log10_input_lt_next_power x ((log10 x).run s).fst := by
  simpa [fixedPointMathLib_log10_input_lt_next_power, logFloor_property] using
    (log10_returns_math_floor x s).2.2

-- tama: discharges=fixedPointMathLib_log10Up_zero_returns_zero
theorem fixedPointMathLib_log10Up_zero_returns_zero_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log10Up_zero_returns_zero x ((log10Up x).run s).fst := by
  intro hZero
  have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
  subst x
  simp [log10Up, Contract.run,
    Tamago.Utils.FixedPointMathLibBase.log10Up, Tamago.Utils.FixedPointMathLibBase.log10,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=fixedPointMathLib_log10Up_input_le_power
theorem fixedPointMathLib_log10Up_input_le_power_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log10Up_input_le_power x ((log10Up x).run s).fst := by
  simpa [fixedPointMathLib_log10Up_input_le_power, logUp_property] using
    (log10Up_returns_math_ceil x s).2.1

-- tama: discharges=fixedPointMathLib_log10Up_prev_power_lt_input
theorem fixedPointMathLib_log10Up_prev_power_lt_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log10Up_prev_power_lt_input x ((log10Up x).run s).fst := by
  simpa [fixedPointMathLib_log10Up_prev_power_lt_input, logUp_property] using
    (log10Up_returns_math_ceil x s).2.2

-- tama: discharges=fixedPointMathLib_log256_zero_returns_zero
theorem fixedPointMathLib_log256_zero_returns_zero_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log256_zero_returns_zero x ((log256 x).run s).fst := by
  intro hZero
  have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
  subst x
  simp [log256, Contract.run, Tamago.Utils.FixedPointMathLibBase.log256, Bind.bind,
    Verity.pure, Pure.pure]

-- tama: discharges=fixedPointMathLib_log256_power_le_input
theorem fixedPointMathLib_log256_power_le_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log256_power_le_input x ((log256 x).run s).fst := by
  simpa [fixedPointMathLib_log256_power_le_input, logFloor_property] using
    (log256_returns_math_floor x s).2.1

-- tama: discharges=fixedPointMathLib_log256_input_lt_next_power
theorem fixedPointMathLib_log256_input_lt_next_power_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log256_input_lt_next_power x ((log256 x).run s).fst := by
  simpa [fixedPointMathLib_log256_input_lt_next_power, logFloor_property] using
    (log256_returns_math_floor x s).2.2

-- tama: discharges=fixedPointMathLib_log256Up_zero_returns_zero
theorem fixedPointMathLib_log256Up_zero_returns_zero_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log256Up_zero_returns_zero x ((log256Up x).run s).fst := by
  intro hZero
  have hx : x = 0 := Verity.Core.Uint256.ext (by simpa using hZero)
  subst x
  simp [log256Up, Contract.run, Tamago.Utils.FixedPointMathLibBase.log256Up,
    Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=fixedPointMathLib_log256Up_input_le_power
theorem fixedPointMathLib_log256Up_input_le_power_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log256Up_input_le_power x ((log256Up x).run s).fst := by
  simpa [fixedPointMathLib_log256Up_input_le_power, logUp_property] using
    (log256Up_returns_math_ceil x s).2.1

-- tama: discharges=fixedPointMathLib_log256Up_prev_power_lt_input
theorem fixedPointMathLib_log256Up_prev_power_lt_input_holds (x : Uint256) (s : ContractState) :
    fixedPointMathLib_log256Up_prev_power_lt_input x ((log256Up x).run s).fst := by
  simpa [fixedPointMathLib_log256Up_prev_power_lt_input, logUp_property] using
    (log256Up_returns_math_ceil x s).2.2

-- tama: discharges=fixedPointMathLib_clamp_invalid_range_returns_max
theorem fixedPointMathLib_clamp_invalid_range_returns_max_holds
    (x minValue maxValue : Uint256) (s : ContractState) :
    fixedPointMathLib_clamp_invalid_range_returns_max
      x minValue maxValue ((clamp x minValue maxValue).run s).fst := by
  simpa [fixedPointMathLib_clamp_invalid_range_returns_max, clamp_property] using
    (clamp_stays_within_bounds x minValue maxValue s).1

-- tama: discharges=fixedPointMathLib_clamp_valid_range_bounds
theorem fixedPointMathLib_clamp_valid_range_bounds_holds
    (x minValue maxValue : Uint256) (s : ContractState) :
    fixedPointMathLib_clamp_valid_range_bounds
      x minValue maxValue ((clamp x minValue maxValue).run s).fst := by
  simpa [fixedPointMathLib_clamp_valid_range_bounds, clamp_property] using
    (clamp_stays_within_bounds x minValue maxValue s).2.1

-- tama: discharges=fixedPointMathLib_clamp_preserves_in_range
theorem fixedPointMathLib_clamp_preserves_in_range_holds
    (x minValue maxValue : Uint256) (s : ContractState) :
    fixedPointMathLib_clamp_preserves_in_range
      x minValue maxValue ((clamp x minValue maxValue).run s).fst := by
  simpa [fixedPointMathLib_clamp_preserves_in_range, clamp_property] using
    (clamp_stays_within_bounds x minValue maxValue s).2.2.1

-- tama: discharges=fixedPointMathLib_clamp_below_min_returns_min
theorem fixedPointMathLib_clamp_below_min_returns_min_holds
    (x minValue maxValue : Uint256) (s : ContractState) :
    fixedPointMathLib_clamp_below_min_returns_min
      x minValue maxValue ((clamp x minValue maxValue).run s).fst := by
  simpa [fixedPointMathLib_clamp_below_min_returns_min, clamp_property] using
    (clamp_stays_within_bounds x minValue maxValue s).2.2.2.1

-- tama: discharges=fixedPointMathLib_clamp_above_max_returns_max
theorem fixedPointMathLib_clamp_above_max_returns_max_holds
    (x minValue maxValue : Uint256) (s : ContractState) :
    fixedPointMathLib_clamp_above_max_returns_max
      x minValue maxValue ((clamp x minValue maxValue).run s).fst := by
  simpa [fixedPointMathLib_clamp_above_max_returns_max, clamp_property] using
    (clamp_stays_within_bounds x minValue maxValue s).2.2.2.2

end Tamago.Proof.Utils.FixedPointMathLibProof
