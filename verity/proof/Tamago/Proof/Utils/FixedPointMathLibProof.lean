import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tamago.Spec.Utils.FixedPointMathLibSpec
import Verity.Proofs.Stdlib.Automation

namespace Tamago.Proof.Utils.FixedPointMathLibProof

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open Verity
open Verity.EVM.Uint256
open Tamago.Utils
open Tamago.Spec.Utils.FixedPointMathLibSpec
open Tamago.Utils.FixedPointMathLib

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

private def sqrtCorrectNat (x z : Nat) : Nat :=
  if x / z < z then z - 1 else z

private def sqrtStepNat (x z : Nat) : Nat :=
  (z + x / z) / 2

private def sqrtIterNat : Nat → Nat → Nat → Nat
  | 0, _x, z => z
  | steps + 1, x, z => sqrtIterNat steps x (sqrtStepNat x z)

private def sqrtScanStepNat (x r shift : Nat) : Nat :=
  if 2 ^ (shift + 8) - 1 < x / 2 ^ r then r + shift else r

private def sqrtScanNat (x : Nat) : Nat :=
  let r := sqrtScanStepNat x 0 128
  let r := sqrtScanStepNat x r 64
  let r := sqrtScanStepNat x r 32
  sqrtScanStepNat x r 16

private theorem pow2_div_lower_from_div_lower (x r a b : Nat)
    (h : 2 ^ (a + b) ≤ x / 2 ^ r) :
    2 ^ a ≤ x / 2 ^ (r + b) := by
  have hMul : 2 ^ (a + b) * 2 ^ r ≤ x :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 2))).1 h
  have hGoalMul : 2 ^ a * 2 ^ (r + b) ≤ x := by
    have hEq : 2 ^ a * 2 ^ (r + b) = 2 ^ (a + b) * 2 ^ r := by
      rw [Nat.pow_add, Nat.pow_add]
      ring
    rw [hEq]
    exact hMul
  exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 2))).2 hGoalMul

private theorem pow2_div_upper_from_value_upper (value a b : Nat)
    (h : value < 2 ^ (a + b)) :
    value / 2 ^ b < 2 ^ a := by
  have hMul : 2 ^ (a + b) = 2 ^ b * 2 ^ a := by
    rw [Nat.pow_add]
    ring
  rw [hMul] at h
  exact Nat.div_lt_of_lt_mul h

private theorem sqrtScanStepNat_lower_bound
    (x r shift : Nat)
    (hLower : 2 ^ 8 ≤ x / 2 ^ r) :
    2 ^ 8 ≤ x / 2 ^ sqrtScanStepNat x r shift := by
  unfold sqrtScanStepNat
  by_cases hBranch : 2 ^ (shift + 8) - 1 < x / 2 ^ r
  · have hBranchLe : 2 ^ (8 + shift) ≤ x / 2 ^ r := by
      have hEq : 2 ^ (8 + shift) = 2 ^ (shift + 8) := by
        rw [Nat.add_comm]
      rw [hEq]
      omega
    have hLower' : 2 ^ 8 ≤ x / 2 ^ (r + shift) :=
      pow2_div_lower_from_div_lower x r 8 shift hBranchLe
    simpa [hBranch] using hLower'
  · simpa [hBranch] using hLower

private theorem sqrtScanStepNat_upper_bound
    (x r shift : Nat)
    (hUpper : x / 2 ^ r < 2 ^ (shift + (shift + 8))) :
    x / 2 ^ sqrtScanStepNat x r shift < 2 ^ (shift + 8) := by
  unfold sqrtScanStepNat
  by_cases hBranch : 2 ^ (shift + 8) - 1 < x / 2 ^ r
  · have hBranchLe : 2 ^ (8 + shift) ≤ x / 2 ^ r := by
      have hEq : 2 ^ (8 + shift) = 2 ^ (shift + 8) := by
        rw [Nat.add_comm]
      rw [hEq]
      omega
    have hUpper' : x / 2 ^ (r + shift) < 2 ^ (shift + 8) := by
      have hUpperReordered : x / 2 ^ r < 2 ^ (shift + 8 + shift) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpper
      have h : x / 2 ^ r / 2 ^ shift < 2 ^ (shift + 8) :=
        pow2_div_upper_from_value_upper (x / 2 ^ r) (shift + 8) shift hUpperReordered
      simpa [Nat.div_div_eq_div_mul, ← Nat.pow_add] using h
    simpa [hBranch] using hUpper'
  · have hUpper' : x / 2 ^ r < 2 ^ (shift + 8) := by
      have hPowPos : 0 < 2 ^ (shift + 8) := Nat.pow_pos (by decide : 0 < 2)
      omega
    simpa [hBranch] using hUpper'

private theorem sqrtScanNat_lower_bound (x : Nat) (hx : 2 ^ 8 ≤ x) :
    2 ^ 8 ≤ x / 2 ^ sqrtScanNat x := by
  let r1 := sqrtScanStepNat x 0 128
  have h1 : 2 ^ 8 ≤ x / 2 ^ r1 := by
    simpa [r1] using sqrtScanStepNat_lower_bound x 0 128 (by simpa using hx)
  let r2 := sqrtScanStepNat x r1 64
  have h2 : 2 ^ 8 ≤ x / 2 ^ r2 := by
    simpa [r2] using sqrtScanStepNat_lower_bound x r1 64 h1
  let r3 := sqrtScanStepNat x r2 32
  have h3 : 2 ^ 8 ≤ x / 2 ^ r3 := by
    simpa [r3] using sqrtScanStepNat_lower_bound x r2 32 h2
  let r4 := sqrtScanStepNat x r3 16
  have h4 : 2 ^ 8 ≤ x / 2 ^ r4 := by
    simpa [r4] using sqrtScanStepNat_lower_bound x r3 16 h3
  simpa [sqrtScanNat, r1, r2, r3, r4] using h4

private theorem sqrtScanNat_upper_bound (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    x / 2 ^ sqrtScanNat x < 2 ^ 24 := by
  have h0Lower : 2 ^ 8 ≤ x / 2 ^ 0 := by simpa using hx
  have h0Upper : x / 2 ^ 0 < 2 ^ (128 + (128 + 8)) := by
    exact lt_of_lt_of_le (by simpa using hxLt) (by norm_num)
  let r1 := sqrtScanStepNat x 0 128
  have h1Lower : 2 ^ 8 ≤ x / 2 ^ r1 := by
    simpa [r1] using sqrtScanStepNat_lower_bound x 0 128 h0Lower
  have h1Upper : x / 2 ^ r1 < 2 ^ (128 + 8) := by
    simpa [r1] using sqrtScanStepNat_upper_bound x 0 128 h0Upper
  let r2 := sqrtScanStepNat x r1 64
  have h2Lower : 2 ^ 8 ≤ x / 2 ^ r2 := by
    simpa [r2] using sqrtScanStepNat_lower_bound x r1 64 h1Lower
  have h2Upper : x / 2 ^ r2 < 2 ^ (64 + 8) := by
    have hUpper : x / 2 ^ r1 < 2 ^ (64 + (64 + 8)) :=
      lt_of_lt_of_le h1Upper (by norm_num)
    simpa [r2] using sqrtScanStepNat_upper_bound x r1 64 hUpper
  let r3 := sqrtScanStepNat x r2 32
  have h3Lower : 2 ^ 8 ≤ x / 2 ^ r3 := by
    simpa [r3] using sqrtScanStepNat_lower_bound x r2 32 h2Lower
  have h3Upper : x / 2 ^ r3 < 2 ^ (32 + 8) := by
    have hUpper : x / 2 ^ r2 < 2 ^ (32 + (32 + 8)) :=
      lt_of_lt_of_le h2Upper (by norm_num)
    simpa [r3] using sqrtScanStepNat_upper_bound x r2 32 hUpper
  let r4 := sqrtScanStepNat x r3 16
  have h4Upper : x / 2 ^ r4 < 2 ^ (16 + 8) := by
    have hUpper : x / 2 ^ r3 < 2 ^ (16 + (16 + 8)) :=
      lt_of_lt_of_le h3Upper (by norm_num)
    simpa [r4] using sqrtScanStepNat_upper_bound x r3 16 hUpper
  simpa [sqrtScanNat, r1, r2, r3, r4] using h4Upper

private theorem sqrtScanStepNat_mod_16
    (x r shift : Nat) (hr : r % 16 = 0) (hshift : shift % 16 = 0) :
    (sqrtScanStepNat x r shift) % 16 = 0 := by
  unfold sqrtScanStepNat
  by_cases hBranch : 2 ^ (shift + 8) - 1 < x / 2 ^ r
  · simp [hBranch, Nat.add_mod, hr, hshift]
  · simp [hBranch, hr]

private theorem sqrtScanNat_mod_16 (x : Nat) :
    sqrtScanNat x % 16 = 0 := by
  let r1 := sqrtScanStepNat x 0 128
  have h1 : r1 % 16 = 0 := by
    simpa [r1] using sqrtScanStepNat_mod_16 x 0 128 (by norm_num) (by norm_num)
  let r2 := sqrtScanStepNat x r1 64
  have h2 : r2 % 16 = 0 := by
    simpa [r2] using sqrtScanStepNat_mod_16 x r1 64 h1 (by norm_num)
  let r3 := sqrtScanStepNat x r2 32
  have h3 : r3 % 16 = 0 := by
    simpa [r3] using sqrtScanStepNat_mod_16 x r2 32 h2 (by norm_num)
  let r4 := sqrtScanStepNat x r3 16
  have h4 : r4 % 16 = 0 := by
    simpa [r4] using sqrtScanStepNat_mod_16 x r3 16 h3 (by norm_num)
  simpa [sqrtScanNat, r1, r2, r3, r4] using h4

private theorem sqrtScanNat_even (x : Nat) :
    2 ∣ sqrtScanNat x := by
  have h16 : 16 ∣ sqrtScanNat x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact sqrtScanNat_mod_16 x
  exact dvd_trans (by norm_num : 2 ∣ 16) h16

private theorem sqrtScanNat_pow_half_sq (x : Nat) :
    2 ^ (sqrtScanNat x / 2) * 2 ^ (sqrtScanNat x / 2) =
      2 ^ sqrtScanNat x := by
  have hEven := sqrtScanNat_even x
  have hMul : 2 * (sqrtScanNat x / 2) = sqrtScanNat x :=
    Nat.mul_div_cancel' hEven
  have hAdd : sqrtScanNat x / 2 + sqrtScanNat x / 2 = sqrtScanNat x := by
    omega
  rw [← Nat.pow_add, hAdd]

private theorem sqrtSeedApprox_upper
    (y : Nat) (hyLower : 2 ^ 8 ≤ y) (hyUpper : y < 2 ^ 24) :
    ((181 : ℝ) * ((y : ℝ) + 65536) / (2 ^ 18 : ℝ)) ≤
      ((23 : ℝ) / 8) * Real.sqrt (y : ℝ) := by
  have hyNonneg : 0 ≤ (y : ℝ) := by positivity
  have hyLowerR : (256 : ℝ) ≤ y := by exact_mod_cast hyLower
  have hyUpperR : (y : ℝ) < 16777216 := by
    norm_num at hyUpper ⊢
    exact_mod_cast hyUpper
  have hMain : ((y : ℝ) + 65536) ^ 2 ≤ 259 * 65536 * (y : ℝ) := by
    by_cases hyLe : (y : ℝ) ≤ 65536
    · nlinarith [hyLowerR, hyLe]
    · have hyGe : (65536 : ℝ) ≤ y := le_of_not_ge hyLe
      nlinarith [hyGe, le_of_lt hyUpperR]
  have hPoly :
      ((181 : ℝ) * ((y : ℝ) + 65536) * 8) ^ 2 ≤
        (23 ^ 2 : ℝ) * (2 ^ 18 : ℝ) ^ 2 * (y : ℝ) := by
    nlinarith
  have hSq :
      (((181 : ℝ) * ((y : ℝ) + 65536) / (2 ^ 18 : ℝ)) ^ 2) ≤
        (((23 : ℝ) / 8) * Real.sqrt (y : ℝ)) ^ 2 := by
    have hSqrtSq : (Real.sqrt (y : ℝ)) ^ 2 = (y : ℝ) :=
      Real.sq_sqrt hyNonneg
    field_simp
    nlinarith
  have hLeftNonneg :
      0 ≤ ((181 : ℝ) * ((y : ℝ) + 65536) / (2 ^ 18 : ℝ)) := by positivity
  have hRightNonneg :
      0 ≤ ((23 : ℝ) / 8) * Real.sqrt (y : ℝ) := by positivity
  have hAbs := sq_le_sq.mp hSq
  rwa [abs_of_nonneg hLeftNonneg, abs_of_nonneg hRightNonneg] at hAbs

private theorem sqrtSeedApprox_lower
    (y : Nat) (hyLower : 2 ^ 8 ≤ y) :
    ((8 : ℝ) / 23) * Real.sqrt ((y : ℝ) + 1) + 1 ≤
      ((181 : ℝ) * ((y : ℝ) + 65536) / (2 ^ 18 : ℝ)) := by
  have hyLowerR : (256 : ℝ) ≤ y := by exact_mod_cast hyLower
  have hPoly :
      (1024 : ℝ) * 65536 ^ 2 * ((y : ℝ) + 1) ≤
        529 * (181 * (y : ℝ) + 177 * 65536) ^ 2 := by
    have hSq :
        0 ≤ (2 * (17330569 : ℝ) * (y : ℝ) - 2176694222848) ^ 2 :=
      sq_nonneg _
    nlinarith
  have hRightNonneg :
      0 ≤ ((181 : ℝ) * ((y : ℝ) + 65536) / (2 ^ 18 : ℝ) - 1) := by
    nlinarith
  have hLeftNonneg : 0 ≤ ((8 : ℝ) / 23) * Real.sqrt ((y : ℝ) + 1) := by
    positivity
  have hSq :
      (((8 : ℝ) / 23) * Real.sqrt ((y : ℝ) + 1)) ^ 2 ≤
        (((181 : ℝ) * ((y : ℝ) + 65536) / (2 ^ 18 : ℝ) - 1) ^ 2) := by
    have hSqrtSq : (Real.sqrt ((y : ℝ) + 1)) ^ 2 = (y : ℝ) + 1 := by
      exact Real.sq_sqrt (by positivity)
    field_simp
    nlinarith
  have hAbs := sq_le_sq.mp hSq
  rw [abs_of_nonneg hLeftNonneg, abs_of_nonneg hRightNonneg] at hAbs
  linarith

private theorem real_mul_sqrt_le_sqrt
    {q y x : ℝ} (hq : 0 ≤ q) (hy : 0 ≤ y) (hx : 0 ≤ x)
    (h : q * q * y ≤ x) :
    q * Real.sqrt y ≤ Real.sqrt x := by
  have hLeftNonneg : 0 ≤ q * Real.sqrt y := by positivity
  have hRightNonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hSq : (q * Real.sqrt y) ^ 2 ≤ (Real.sqrt x) ^ 2 := by
    have hySq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
    have hxSq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
    nlinarith
  have hAbs := sq_le_sq.mp hSq
  rwa [abs_of_nonneg hLeftNonneg, abs_of_nonneg hRightNonneg] at hAbs

private theorem real_sqrt_le_mul_sqrt
    {q y x : ℝ} (hq : 0 ≤ q) (hy : 0 ≤ y) (hx : 0 ≤ x)
    (h : x ≤ q * q * y) :
    Real.sqrt x ≤ q * Real.sqrt y := by
  have hLeftNonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hRightNonneg : 0 ≤ q * Real.sqrt y := by positivity
  have hSq : (Real.sqrt x) ^ 2 ≤ (q * Real.sqrt y) ^ 2 := by
    have hySq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
    have hxSq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
    nlinarith
  have hAbs := sq_le_sq.mp hSq
  rwa [abs_of_nonneg hLeftNonneg, abs_of_nonneg hRightNonneg] at hAbs

private def soladySqrtSeedNat (x : Nat) : Nat :=
  let r := sqrtScanNat x
  (181 * 2 ^ (r / 2) * (x / 2 ^ r + 65536)) / 2 ^ 18

private theorem soladySqrtSeedNat_real_bounds
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    0 < soladySqrtSeedNat x ∧
      (1 / ((23 : ℝ) / 8) ≤
        (soladySqrtSeedNat x : ℝ) / Real.sqrt (x : ℝ)) ∧
      ((soladySqrtSeedNat x : ℝ) / Real.sqrt (x : ℝ) ≤ (23 : ℝ) / 8) := by
  let r := sqrtScanNat x
  let y := x / 2 ^ r
  let q := 2 ^ (r / 2)
  let n := 181 * q * (y + 65536)
  let d := 2 ^ 18
  have hyLower : 2 ^ 8 ≤ y := by
    simpa [r, y] using sqrtScanNat_lower_bound x hx
  have hyUpper : y < 2 ^ 24 := by
    simpa [r, y] using sqrtScanNat_upper_bound x hx hxLt
  have hdPosNat : 0 < d := by
    norm_num [d]
  have hqPosNat : 0 < q := by
    dsimp [q]
    exact Nat.pow_pos (by decide : 0 < 2)
  have hqGeOneNat : 1 ≤ q := Nat.succ_le_of_lt hqPosNat
  have hxPosNat : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hxPosReal : 0 < (x : ℝ) := Nat.cast_pos.2 hxPosNat
  have hSqrtPos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.2 hxPosReal
  have hqSqNat : q * q = 2 ^ r := by
    simpa [r, q] using sqrtScanNat_pow_half_sq x
  have hXLowerNat : q * q * y ≤ x := by
    have hDivMul : y * 2 ^ r ≤ x := by
      simpa [y] using Nat.div_mul_le_self x (2 ^ r)
    rw [hqSqNat]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hDivMul
  have hXUpperNat : x < q * q * (y + 1) := by
    have hUpper := Nat.lt_mul_div_succ x
      (show 0 < 2 ^ r from Nat.pow_pos (by decide : 0 < 2))
    have hUpper' : x < (y + 1) * 2 ^ r := by
      simpa [y, Nat.mul_comm] using hUpper
    rw [← hqSqNat] at hUpper'
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hUpper'
  have hSeedEq :
      soladySqrtSeedNat x = n / d := by
    simp [soladySqrtSeedNat, r, y, q, n, d]
  have hNReal :
      (n : ℝ) / (d : ℝ) =
        (q : ℝ) * (((181 : ℝ) * ((y : ℝ) + 65536)) / (2 ^ 18 : ℝ)) := by
    simp [n, d]
    ring
  have hFloorUpper :
      ((n / d : Nat) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hFloorLower :
      (n : ℝ) / (d : ℝ) - 1 < (n / d : Nat) := by
    have hSucc := Nat.lt_mul_div_succ n hdPosNat
    have hSuccR : (n : ℝ) < (d : ℝ) * ((n / d : Nat) + 1) := by
      exact_mod_cast hSucc
    have hdPosR : 0 < (d : ℝ) := Nat.cast_pos.2 hdPosNat
    nlinarith
  have hQsqrtLower :
      (q : ℝ) * Real.sqrt (y : ℝ) ≤ Real.sqrt (x : ℝ) := by
    apply real_mul_sqrt_le_sqrt
    · positivity
    · positivity
    · positivity
    · exact_mod_cast hXLowerNat
  have hSqrtUpper :
      Real.sqrt (x : ℝ) ≤ (q : ℝ) * Real.sqrt ((y : ℝ) + 1) := by
    apply real_sqrt_le_mul_sqrt
    · positivity
    · positivity
    · positivity
    · exact_mod_cast (le_of_lt hXUpperNat)
  have hApproxUpper := sqrtSeedApprox_upper y hyLower hyUpper
  have hApproxLower := sqrtSeedApprox_lower y hyLower
  have hSeedUpper :
      (soladySqrtSeedNat x : ℝ) ≤ ((23 : ℝ) / 8) * Real.sqrt (x : ℝ) := by
    rw [hSeedEq]
    calc
      ((n / d : Nat) : ℝ) ≤ (n : ℝ) / (d : ℝ) := hFloorUpper
      _ = (q : ℝ) * (((181 : ℝ) * ((y : ℝ) + 65536)) / (2 ^ 18 : ℝ)) := hNReal
      _ ≤ (q : ℝ) * (((23 : ℝ) / 8) * Real.sqrt (y : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hApproxUpper (by positivity)
      _ ≤ ((23 : ℝ) / 8) * Real.sqrt (x : ℝ) := by
        nlinarith
  have hSeedLower :
      ((8 : ℝ) / 23) * Real.sqrt (x : ℝ) ≤ (soladySqrtSeedNat x : ℝ) := by
    rw [hSeedEq]
    calc
      ((8 : ℝ) / 23) * Real.sqrt (x : ℝ)
          ≤ ((8 : ℝ) / 23) * ((q : ℝ) * Real.sqrt ((y : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_left hSqrtUpper (by norm_num)
      _ ≤ (q : ℝ) *
            (((181 : ℝ) * ((y : ℝ) + 65536)) / (2 ^ 18 : ℝ)) - 1 := by
            have hqGeOne : (1 : ℝ) ≤ q := by exact_mod_cast hqGeOneNat
            nlinarith
      _ = (n : ℝ) / (d : ℝ) - 1 := by rw [hNReal]
      _ ≤ ((n / d : Nat) : ℝ) := le_of_lt hFloorLower
  have hSeedPos : 0 < soladySqrtSeedNat x := by
    have hPositiveReal : (0 : ℝ) < soladySqrtSeedNat x := by
      have hLowerPos : (0 : ℝ) < ((8 : ℝ) / 23) * Real.sqrt (x : ℝ) := by positivity
      exact lt_of_lt_of_le hLowerPos hSeedLower
    exact Nat.cast_pos.1 hPositiveReal
  refine ⟨hSeedPos, ?_, ?_⟩
  · have h : ((8 : ℝ) / 23) ≤ (soladySqrtSeedNat x : ℝ) / Real.sqrt (x : ℝ) := by
      rw [le_div_iff₀ hSqrtPos]
      exact hSeedLower
    norm_num
    simpa using h
  · rw [div_le_iff₀ hSqrtPos]
    exact hSeedUpper

private def soladySqrtBeforeCorrectionNat (x : Nat) : Nat :=
  sqrtIterNat 7 x (soladySqrtSeedNat x)

private def soladySqrtNat (x : Nat) : Nat :=
  sqrtCorrectNat x (soladySqrtBeforeCorrectionNat x)

private theorem soladySqrtNat_property_small :
    ∀ x : Fin 256,
      soladySqrtNat x.val * soladySqrtNat x.val ≤ x.val ∧
        x.val < (soladySqrtNat x.val + 1) * (soladySqrtNat x.val + 1) := by
  native_decide

private theorem soladySqrtNat_property_of_lt_256 (x : Nat) (hx : x < 256) :
    soladySqrtNat x * soladySqrtNat x ≤ x ∧
      x < (soladySqrtNat x + 1) * (soladySqrtNat x + 1) := by
  simpa using soladySqrtNat_property_small ⟨x, hx⟩

private theorem sqrtCorrectNat_property
    (x z : Nat) (hz : 0 < z)
    (hLower : (z - 1) * (z - 1) ≤ x)
    (hUpper : x < (z + 1) * (z + 1)) :
    sqrtCorrectNat x z * sqrtCorrectNat x z ≤ x ∧
      x < (sqrtCorrectNat x z + 1) * (sqrtCorrectNat x z + 1) := by
  unfold sqrtCorrectNat
  by_cases hBranch : x / z < z
  · have hUpper' : x < z * z := by
      exact (Nat.div_lt_iff_lt_mul hz).1 hBranch
    have hSuccPred : z - 1 + 1 = z := Nat.sub_add_cancel hz
    simpa [hBranch, hSuccPred] using And.intro hLower hUpper'
  · have hLower' : z * z ≤ x := by
      have hLe : z ≤ x / z := Nat.le_of_not_gt hBranch
      exact (Nat.le_div_iff_mul_le hz).1 hLe
    simp [hBranch, hLower', hUpper]

private theorem sqrtStepNat_ge_floor (x z : Nat) (hz : 0 < z) :
    Nat.sqrt x ≤ sqrtStepNat x z := by
  unfold sqrtStepNat
  let a := Nat.sqrt x
  have ha2 : a * a ≤ x := by
    simpa [a] using Nat.sqrt_le x
  have hsum : a * 2 ≤ z + x / z := by
    by_cases hzle : z ≤ 2 * a
    · have hmul : (2 * a - z) * z ≤ a * a := by
        have hmulInt :
            ((2 * a - z : Nat) : Int) * (z : Int) ≤ (a : Int) * (a : Int) := by
          have hcast :
              ((2 * a - z : Nat) : Int) = 2 * (a : Int) - (z : Int) := by
            exact Nat.cast_sub hzle
          rw [hcast]
          nlinarith [sq_nonneg ((z : Int) - (a : Int))]
        exact_mod_cast hmulInt
      have hmulX : (2 * a - z) * z ≤ x := le_trans hmul ha2
      have hdiv : 2 * a - z ≤ x / z :=
        (Nat.le_div_iff_mul_le hz).2 hmulX
      omega
    · have hgt : 2 * a < z := Nat.lt_of_not_ge hzle
      have hle : a * 2 ≤ z := by omega
      exact le_trans hle (Nat.le_add_right _ _)
  have hdiv2 : a ≤ (z + x / z) / 2 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by
      simpa [Nat.mul_comm] using hsum)
  simpa [a] using hdiv2

private theorem sqrtStepNat_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) :
    0 < sqrtStepNat x z := by
  unfold sqrtStepNat
  cases z with
  | zero => cases hz
  | succ z' =>
      cases z' with
      | zero =>
          have hDiv : x / 1 = x := Nat.div_one x
          rw [hDiv]
          exact Nat.div_pos (by omega) (by decide : 0 < 2)
      | succ z'' =>
          have hNum :
              2 ≤ Nat.succ (Nat.succ z'') + x / Nat.succ (Nat.succ z'') :=
            Nat.le_add_right_of_le (by omega)
          exact Nat.div_pos hNum (by decide : 0 < 2)

private theorem sqrtNewtonRatioUpper
    {u t : ℝ} (hu : 1 ≤ u) (htPos : 0 < t)
    (htLower : 1 / u ≤ t) (htUpper : t ≤ u) :
    (t + 1 / t) / 2 ≤ (u + 1 / u) / 2 := by
  have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have htNe : t ≠ 0 := ne_of_gt htPos
  have huNe : u ≠ 0 := ne_of_gt huPos
  have hUminus : 0 ≤ u - t := sub_nonneg.mpr htUpper
  have hUt : 1 ≤ u * t := by
    have hMul := mul_le_mul_of_nonneg_left htLower (le_of_lt huPos)
    have hLeft : u * (1 / u) = 1 := by field_simp [huNe]
    linarith
  have hUtminus : 0 ≤ u * t - 1 := sub_nonneg.mpr hUt
  have hprod : 0 ≤ (u - t) * (u * t - 1) := mul_nonneg hUminus hUtminus
  have hden : 0 < u * t := mul_pos huPos htPos
  have hmain : 0 ≤ (u + 1 / u) - (t + 1 / t) := by
    have hEq :
        (u + 1 / u) - (t + 1 / t) = ((u - t) * (u * t - 1)) / (u * t) := by
      field_simp [huNe, htNe]
      ring
    rw [hEq]
    exact div_nonneg hprod (le_of_lt hden)
  linarith

private def sqrtNewtonBoundRat : Nat → ℚ
  | 0 => (23 : ℚ) / 8
  | steps + 1 =>
      let u := sqrtNewtonBoundRat steps
      (u + 1 / u) / 2

private theorem sqrtNewtonBoundRat_ge_one (steps : Nat) :
    1 ≤ sqrtNewtonBoundRat steps := by
  induction steps with
  | zero => native_decide
  | succ steps ih =>
      dsimp [sqrtNewtonBoundRat]
      let u := sqrtNewtonBoundRat steps
      have hu : 1 ≤ u := ih
      have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have h : 2 ≤ u + 1 / u := by
        have hnonneg : 0 ≤ (u - 1) * (u - 1) / u :=
          div_nonneg (mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)) (le_of_lt huPos)
        have hEq : u + 1 / u - 2 = (u - 1) * (u - 1) / u := by
          field_simp [ne_of_gt huPos]
          ring
        linarith
      linarith

private theorem sqrtNewtonBoundRat_pos (steps : Nat) :
    0 < sqrtNewtonBoundRat steps :=
  lt_of_lt_of_le zero_lt_one (sqrtNewtonBoundRat_ge_one steps)

private theorem sqrtNewtonBoundRat_seven_tight :
    sqrtNewtonBoundRat 7 < (1 : ℚ) + 1 / ((2 : ℚ) ^ 128) := by
  native_decide

private theorem sqrtNewtonBoundRat_seven_real_tight :
    ((sqrtNewtonBoundRat 7 : ℚ) : ℝ) < (1 : ℝ) + 1 / ((2 : ℝ) ^ 128) := by
  have hRhs :
      (((1 : ℚ) + 1 / ((2 : ℚ) ^ 128) : ℚ) : ℝ) =
        (1 : ℝ) + 1 / ((2 : ℝ) ^ 128) := by
    norm_num
  rw [← hRhs]
  exact Rat.cast_lt.2 sqrtNewtonBoundRat_seven_tight

private theorem sqrtStepNat_real_ratio_upper
    (x z : Nat) (hx : 0 < x) (hz : 0 < z) {u : ℝ}
    (hu : 1 ≤ u)
    (hLowerRatio : 1 / u ≤ (z : ℝ) / Real.sqrt (x : ℝ))
    (hUpperRatio : (z : ℝ) / Real.sqrt (x : ℝ) ≤ u) :
    (sqrtStepNat x z : ℝ) ≤ ((u + 1 / u) / 2) * Real.sqrt (x : ℝ) := by
  let α := Real.sqrt (x : ℝ)
  have hxRealPos : 0 < (x : ℝ) := Nat.cast_pos.2 hx
  have hαPos : 0 < α := by
    simpa [α] using Real.sqrt_pos.2 hxRealPos
  have hαNe : α ≠ 0 := ne_of_gt hαPos
  have hzRealPos : 0 < (z : ℝ) := Nat.cast_pos.2 hz
  have hzRealNe : (z : ℝ) ≠ 0 := ne_of_gt hzRealPos
  have hStepCast : (sqrtStepNat x z : ℝ) ≤ ((z + x / z : Nat) : ℝ) / 2 := by
    unfold sqrtStepNat
    exact Nat.cast_div_le
  have hDivCast : ((x / z : Nat) : ℝ) ≤ (x : ℝ) / (z : ℝ) := Nat.cast_div_le
  have hAddCast :
      ((z + x / z : Nat) : ℝ) / 2 ≤ ((z : ℝ) + (x : ℝ) / (z : ℝ)) / 2 := by
    norm_num
    nlinarith [hDivCast]
  have hRealStep :
      ((z : ℝ) + (x : ℝ) / (z : ℝ)) / 2 =
        (((z : ℝ) / α + 1 / ((z : ℝ) / α)) / 2) * α := by
    have hsq : α ^ 2 = (x : ℝ) := by
      dsimp [α]
      exact Real.sq_sqrt (le_of_lt hxRealPos)
    rw [← hsq]
    field_simp [hαNe, hzRealNe]
    ring
  have htPos : 0 < (z : ℝ) / α := div_pos hzRealPos hαPos
  have hRatio := sqrtNewtonRatioUpper (u := u) (t := (z : ℝ) / α)
    hu htPos (by simpa [α] using hLowerRatio) (by simpa [α] using hUpperRatio)
  have hMul := mul_le_mul_of_nonneg_right hRatio (le_of_lt hαPos)
  calc
    (sqrtStepNat x z : ℝ) ≤ ((z + x / z : Nat) : ℝ) / 2 := hStepCast
    _ ≤ ((z : ℝ) + (x : ℝ) / (z : ℝ)) / 2 := hAddCast
    _ = (((z : ℝ) / α + 1 / ((z : ℝ) / α)) / 2) * α := hRealStep
    _ ≤ ((u + 1 / u) / 2) * α := hMul
    _ = ((u + 1 / u) / 2) * Real.sqrt (x : ℝ) := rfl

private theorem sqrt_near_floor_property
    (x z : Nat)
    (hLower : Nat.sqrt x ≤ z)
    (hUpper : z ≤ Nat.sqrt x + 1) :
    (z - 1) * (z - 1) ≤ x ∧ x < (z + 1) * (z + 1) := by
  constructor
  · have hzPred : z - 1 ≤ Nat.sqrt x := by omega
    exact le_trans (Nat.mul_le_mul hzPred hzPred) (Nat.sqrt_le x)
  · have hSuccLe : Nat.sqrt x + 1 ≤ z + 1 := by omega
    exact lt_of_lt_of_le (Nat.lt_succ_sqrt x) (Nat.mul_le_mul hSuccLe hSuccLe)

private theorem sqrtStepNat_near_of_near
    (x z : Nat) (hx : 0 < x)
    (hLower : Nat.sqrt x ≤ z)
    (hUpper : z ≤ Nat.sqrt x + 1) :
    sqrtStepNat x z ≤ Nat.sqrt x + 1 := by
  let a := Nat.sqrt x
  have haPos : 0 < a := by
    have hx1 : 1 ≤ x := hx
    have h : 1 * 1 ≤ x := by simpa using hx1
    exact (Nat.le_sqrt).2 h
  have hzCases : z = a ∨ z = a + 1 := by omega
  rcases hzCases with hzEq | hzEq
  · have hDivA : x / a ≤ a + 2 := by
      have hMulLt : x < a * (a + 3) := by
        have hSqrt := Nat.lt_succ_sqrt x
        nlinarith
      have hDivLt : x / a < a + 3 := (Nat.div_lt_iff_lt_mul haPos).2 (by
        simpa [Nat.mul_comm] using hMulLt)
      omega
    unfold sqrtStepNat
    rw [hzEq]
    have hNum : a + x / a ≤ 2 * (a + 1) := by omega
    exact Nat.div_le_of_le_mul hNum
  · have hDivA : x / (a + 1) ≤ a := by
      have hDivLt : x / (a + 1) < a + 1 :=
        (Nat.div_lt_iff_lt_mul (Nat.succ_pos a)).2 (by
          simpa [Nat.pow_two, Nat.mul_assoc] using Nat.lt_succ_sqrt x)
      omega
    unfold sqrtStepNat
    rw [hzEq]
    have hNum : a + 1 + x / (a + 1) ≤ 2 * (a + 1) := by omega
    exact Nat.div_le_of_le_mul hNum

private theorem sqrtIterNat_near_or_bound
    (steps k x z : Nat) (hx : 0 < x) (hz : 0 < z)
    (hFloor : Nat.sqrt x ≤ z)
    (hState :
      z ≤ Nat.sqrt x + 1 ∨
        (z : ℝ) ≤ ((sqrtNewtonBoundRat k : ℚ) : ℝ) * Real.sqrt (x : ℝ)) :
    Nat.sqrt x ≤ sqrtIterNat steps x z ∧
      (sqrtIterNat steps x z ≤ Nat.sqrt x + 1 ∨
        (sqrtIterNat steps x z : ℝ) ≤
          ((sqrtNewtonBoundRat (k + steps) : ℚ) : ℝ) * Real.sqrt (x : ℝ)) := by
  induction steps generalizing k z with
  | zero =>
      simpa using And.intro hFloor hState
  | succ steps ih =>
      let z1 := sqrtStepNat x z
      have hz1Floor : Nat.sqrt x ≤ z1 := by
        simpa [z1] using sqrtStepNat_ge_floor x z hz
      have hz1Pos : 0 < z1 := by
        simpa [z1] using sqrtStepNat_pos x z hx hz
      have hz1State :
          z1 ≤ Nat.sqrt x + 1 ∨
            (z1 : ℝ) ≤ ((sqrtNewtonBoundRat (k + 1) : ℚ) : ℝ) *
              Real.sqrt (x : ℝ) := by
        rcases hState with hNear | hBound
        · left
          simpa [z1] using sqrtStepNat_near_of_near x z hx hFloor hNear
        · by_cases hNear : z ≤ Nat.sqrt x + 1
          · left
            simpa [z1] using sqrtStepNat_near_of_near x z hx hFloor hNear
          · right
            let u : ℝ := ((sqrtNewtonBoundRat k : ℚ) : ℝ)
            have hu : 1 ≤ u := by
              simpa [u] using Rat.cast_le.2 (sqrtNewtonBoundRat_ge_one k)
            have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
            have hSqrtPos : 0 < Real.sqrt (x : ℝ) := by
              exact Real.sqrt_pos.2 (Nat.cast_pos.2 hx)
            have hUpperRatio : (z : ℝ) / Real.sqrt (x : ℝ) ≤ u := by
              rw [div_le_iff₀ hSqrtPos]
              simpa [u] using hBound
            have hAlphaLtZ : Real.sqrt (x : ℝ) < (z : ℝ) := by
              have hAlphaSucc : Real.sqrt (x : ℝ) < (Nat.sqrt x : ℝ) + 1 :=
                Real.real_sqrt_lt_nat_sqrt_succ
              have hzGt : Nat.sqrt x + 1 < z := Nat.lt_of_not_ge hNear
              exact lt_trans hAlphaSucc (by exact_mod_cast hzGt)
            have hOneLeRatio : (1 : ℝ) ≤ (z : ℝ) / Real.sqrt (x : ℝ) := by
              rw [le_div_iff₀ hSqrtPos]
              simpa [one_mul] using le_of_lt hAlphaLtZ
            have hInvLeOne : (1 : ℝ) / u ≤ 1 := by
              exact (div_le_one huPos).2 hu
            have hLowerRatio : (1 : ℝ) / u ≤ (z : ℝ) / Real.sqrt (x : ℝ) :=
              le_trans hInvLeOne hOneLeRatio
            have hStepUpper := sqrtStepNat_real_ratio_upper
              (x := x) (z := z) hx hz (u := u) hu hLowerRatio hUpperRatio
            have hNext :
                (z1 : ℝ) ≤ ((u + 1 / u) / 2) * Real.sqrt (x : ℝ) := by
              simpa [z1] using hStepUpper
            simpa [z1, u, sqrtNewtonBoundRat] using hNext
      have hTail := ih (k + 1) z1 hz1Pos hz1Floor hz1State
      have hIndex : k + 1 + steps = k + (steps + 1) := by omega
      simpa [sqrtIterNat, z1, hIndex] using hTail

private theorem sqrt_near_of_final_ratio_bound
    (x z : Nat) (hx : 0 < x) (hxLt : x < 2 ^ 256)
    (hBound :
      (z : ℝ) ≤ ((sqrtNewtonBoundRat 7 : ℚ) : ℝ) * Real.sqrt (x : ℝ)) :
    z ≤ Nat.sqrt x + 1 := by
  let α := Real.sqrt (x : ℝ)
  have hαPos : 0 < α := by
    simpa [α] using Real.sqrt_pos.2 (Nat.cast_pos.2 hx)
  have hαLtPow : α < (2 : ℝ) ^ 128 := by
    have hxLtR : (x : ℝ) < (2 : ℝ) ^ 256 := by exact_mod_cast hxLt
    have hPowEq : ((2 : ℝ) ^ 128) ^ 2 = (2 : ℝ) ^ 256 := by
      rw [sq, ← pow_add]
    rw [Real.sqrt_lt' (by positivity : 0 < (2 : ℝ) ^ 128)]
    rw [hPowEq]
    exact hxLtR
  have hTight := sqrtNewtonBoundRat_seven_real_tight
  have hMulTight :
      ((sqrtNewtonBoundRat 7 : ℚ) : ℝ) * α <
        ((1 : ℝ) + 1 / ((2 : ℝ) ^ 128)) * α := by
    exact mul_lt_mul_of_pos_right hTight hαPos
  have hExtra : (1 / ((2 : ℝ) ^ 128)) * α < 1 := by
    rw [one_div_mul_eq_div]
    rw [div_lt_one (by positivity : 0 < (2 : ℝ) ^ 128)]
    exact hαLtPow
  have hZLt : (z : ℝ) < α + 1 := by
    nlinarith [hBound, hMulTight, hExtra]
  have hAlphaSucc : α < (Nat.sqrt x : ℝ) + 1 := by
    simpa [α] using (Real.real_sqrt_lt_nat_sqrt_succ (a := x))
  have hZLtNat : (z : ℝ) < (Nat.sqrt x + 2 : Nat) := by
    have h : α + 1 < (Nat.sqrt x : ℝ) + 2 := by nlinarith
    simpa using lt_trans hZLt h
  have hNat : z < Nat.sqrt x + 2 := by exact_mod_cast hZLtNat
  omega

private theorem soladySqrtBeforeCorrectionNat_near_floor
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    Nat.sqrt x ≤ soladySqrtBeforeCorrectionNat x ∧
      soladySqrtBeforeCorrectionNat x ≤ Nat.sqrt x + 1 := by
  let z0 := soladySqrtSeedNat x
  let z1 := sqrtStepNat x z0
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hSeed := soladySqrtSeedNat_real_bounds x hx hxLt
  have hz0Pos : 0 < z0 := by simpa [z0] using hSeed.1
  have hU0 : (1 : ℝ) ≤ (23 : ℝ) / 8 := by norm_num
  have hStepUpperRaw := sqrtStepNat_real_ratio_upper
    (x := x) (z := z0) hxPos hz0Pos (u := (23 : ℝ) / 8) hU0
    (by simpa [z0] using hSeed.2.1)
    (by simpa [z0] using hSeed.2.2)
  have hz1Bound :
      (z1 : ℝ) ≤ ((sqrtNewtonBoundRat 1 : ℚ) : ℝ) * Real.sqrt (x : ℝ) := by
    simpa [z1, sqrtNewtonBoundRat] using hStepUpperRaw
  have hz1Floor : Nat.sqrt x ≤ z1 := by
    simpa [z1] using sqrtStepNat_ge_floor x z0 hz0Pos
  have hz1Pos : 0 < z1 := by
    simpa [z1] using sqrtStepNat_pos x z0 hxPos hz0Pos
  have hIter := sqrtIterNat_near_or_bound 6 1 x z1 hxPos hz1Pos hz1Floor (Or.inr hz1Bound)
  have hBeforeEq :
      soladySqrtBeforeCorrectionNat x = sqrtIterNat 6 x z1 := by
    simp [soladySqrtBeforeCorrectionNat, z0, z1, sqrtIterNat]
  constructor
  · rw [hBeforeEq]
    exact hIter.1
  · rw [hBeforeEq]
    rcases hIter.2 with hNear | hBound
    · exact hNear
    · have hIndex : 1 + 6 = 7 := by norm_num
      exact sqrt_near_of_final_ratio_bound x (sqrtIterNat 6 x z1) hxPos hxLt (by
        simpa [hIndex] using hBound)

private theorem soladySqrtNat_property (x : Nat) (hxLt : x < 2 ^ 256) :
    soladySqrtNat x * soladySqrtNat x ≤ x ∧
      x < (soladySqrtNat x + 1) * (soladySqrtNat x + 1) := by
  by_cases hxSmall : x < 2 ^ 8
  · exact soladySqrtNat_property_of_lt_256 x (by simpa using hxSmall)
  · have hxLarge : 2 ^ 8 ≤ x := Nat.le_of_not_gt hxSmall
    let z := soladySqrtBeforeCorrectionNat x
    have hNear : Nat.sqrt x ≤ z ∧ z ≤ Nat.sqrt x + 1 := by
      simpa [z] using soladySqrtBeforeCorrectionNat_near_floor x hxLarge hxLt
    have hzPos : 0 < z := by
      have hSqrtPos : 0 < Nat.sqrt x := by
        have h : 1 * 1 ≤ x := by omega
        exact (Nat.le_sqrt).2 h
      exact lt_of_lt_of_le hSqrtPos hNear.1
    have hBounds := sqrt_near_floor_property x z hNear.1 hNear.2
    simpa [soladySqrtNat, z] using
      sqrtCorrectNat_property x z hzPos hBounds.1 hBounds.2

private def cbrt_property (x result : Uint256) : Prop :=
  result.val * result.val * result.val ≤ x.val ∧
  x.val < (result.val + 1) * (result.val + 1) * (result.val + 1)

private def cbrtCorrectNat (x z : Nat) : Nat :=
  if x / (z * z) < z then z - 1 else z

private theorem cbrtCorrectNat_property
    (x z : Nat) (hz : 0 < z)
    (hLower : (z - 1) * (z - 1) * (z - 1) ≤ x)
    (hUpper : x < (z + 1) * (z + 1) * (z + 1)) :
    cbrtCorrectNat x z * cbrtCorrectNat x z * cbrtCorrectNat x z ≤ x ∧
      x < (cbrtCorrectNat x z + 1) * (cbrtCorrectNat x z + 1) *
        (cbrtCorrectNat x z + 1) := by
  unfold cbrtCorrectNat
  have hzz : 0 < z * z := Nat.mul_pos hz hz
  by_cases hBranch : x / (z * z) < z
  · have hUpper' : x < z * (z * z) := by
      exact (Nat.div_lt_iff_lt_mul hzz).1 hBranch
    have hSuccPred : z - 1 + 1 = z := Nat.sub_add_cancel hz
    constructor
    · simpa [hBranch] using hLower
    · simpa [hBranch, hSuccPred, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hUpper'
  · have hLower' : z * z * z ≤ x := by
      have hLe : z ≤ x / (z * z) := Nat.le_of_not_gt hBranch
      have hRaw := (Nat.le_div_iff_mul_le hzz).1 hLe
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hRaw
    simp [hBranch, hLower', hUpper]

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
      simp [saturatingAdd, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hBranchRaw]
    · simp [saturatingAdd, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hBranchRaw, maxUint256_val]
      simpa [Verity.Stdlib.Math.MAX_UINT256] using Verity.Core.Uint256.val_le_max x
    · simp [saturatingAdd, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hBranchRaw, maxUint256_val]
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
      simp [saturatingAdd, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hNotBranchRaw, hAddVal]
    · intro h
      exact False.elim (hOverflow h)
    · simp [saturatingAdd, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hNotBranchRaw, hAddVal]
    · simp [saturatingAdd, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hNotBranchRaw, hAddVal]

theorem saturatingMul_saturates_at_uint256_max (x y : Uint256) (s : ContractState) :
    saturatingMul_property x y ((saturatingMul x y).run s).fst := by
  unfold saturatingMul_property
  by_cases hXZero : x = 0
  · have hxVal : x.val = 0 := by
      simp [hXZero]
    refine ⟨?_, ?_, ?_⟩
    · intro _h
      simp [saturatingMul, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hXZero, hxVal, mul, Verity.Core.Uint256.mul,
        Verity.Core.Uint256.ofNat]
    · intro hOverflow
      have hProdZero : x.val * y.val = 0 := by
        simp [hxVal]
      omega
    · intro _h
      apply Verity.Core.Uint256.ext
      simp [saturatingMul, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hXZero, mul, Verity.Core.Uint256.mul,
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
        simp [saturatingMul, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hXZero, hBranchRaw]
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
        simp [saturatingMul, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hXZero, hNotBranchRaw, hMulVal]
      · intro h
        exact False.elim (hOverflow h)
      · intro hZero
        apply Verity.Core.Uint256.ext
        simp [saturatingMul, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hXZero, hNotBranchRaw, hMulVal]
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
      simp [saturatingSub, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hBranch]
    · intro h
      exact False.elim (hNotLe h)
    · simp [saturatingSub, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hBranch]
  · have hLe : y.val ≤ x.val := by omega
    have hNotBranch : ¬ y > x := by
      exact Nat.not_lt_of_ge hLe
    have hSubVal : (sub x y).val = x.val - y.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := x) (b := y) hLe
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hEq : x.val = y.val := by omega
      apply Verity.Core.Uint256.ext
      simp [saturatingSub, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hNotBranch, hSubVal, hEq]
    · intro _h
      simp [saturatingSub, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hNotBranch, hSubVal]
      omega
    · simp [saturatingSub, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, hNotBranch, hSubVal]

theorem dist_is_absolute_difference (x y : Uint256) (s : ContractState) :
    dist_property x y ((Tamago.Utils.FixedPointMathLib.dist x y).run s).fst := by
  unfold dist_property
  by_cases hGe : y.val ≤ x.val
  · have hBranch : x >= y := hGe
    have hSubVal : (sub x y).val = x.val - y.val := by
      simpa [HSub.hSub] using Verity.Core.Uint256.sub_eq_of_le (a := x) (b := y) hGe
    refine ⟨?_, ?_⟩
    · intro h
      simp [Tamago.Utils.FixedPointMathLib.dist, Contract.run, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure,
        hBranch, hSubVal]
      omega
    · intro _h
      simp [Tamago.Utils.FixedPointMathLib.dist, Contract.run, Verity.bind, Bind.bind, Verity.pure,
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
      simp [Tamago.Utils.FixedPointMathLib.dist, Contract.run, Verity.bind, Bind.bind, Verity.pure,
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
      simp [avg, Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        hBranch, hSubVal, hDivVal, hAddVal]
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
      simp [avg, Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        hNotBranch, hSubVal, hDivVal, hAddVal]
    constructor
    · rw [hRun]
      have hDivLower := two_mul_div_two_le (y.val - x.val)
      omega
    · rw [hRun]
      have hDivUpper := lt_two_mul_div_two_succ (y.val - x.val)
      omega

private def sqrtIterUint : Nat → Uint256 → Uint256 → Uint256
  | 0, _x, z => z
  | steps + 1, x, z => sqrtIterUint steps x (shr 1 (add z (div x z)))

private def sqrtFinishSeedUint (x r z : Uint256) : Uint256 :=
  let z := shl (shr 1 r) z
  shr 18 (mul z (add (shr r x) 65536))

private def sqrtBeforeCorrectionUint (x r z : Uint256) : Uint256 :=
  sqrtIterUint 7 x (sqrtFinishSeedUint x r z)

private def sqrtFinishUint (x r z : Uint256) : Uint256 :=
  let z := sqrtBeforeCorrectionUint x r z
  if div x z < z then sub z 1 else z

private def sqrtFinishContract (x r z : Uint256) : Contract Uint256 :=
  let z := sqrtBeforeCorrectionUint x r z
  if div x z < z then Verity.pure (sub z 1) else Verity.pure z

private def sqrtScan4Contract (x r z : Uint256) : Contract Uint256 :=
  if 16777215 < shr r x then
    let r := Contracts.bitOr r (shl 4 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtFinishContract x r z
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtFinishContract x r z

private def sqrtScan4Uint (x r z : Uint256) : Uint256 :=
  if 16777215 < shr r x then
    sqrtFinishUint x (Contracts.bitOr r (shl 4 1)) z
  else
    sqrtFinishUint x r z

private def sqrtScan5Contract (x r z : Uint256) : Contract Uint256 :=
  if 1099511627775 < shr r x then
    let r := Contracts.bitOr r (shl 5 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtScan4Contract x r z
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtScan4Contract x r z

private def sqrtScan5Uint (x r z : Uint256) : Uint256 :=
  if 1099511627775 < shr r x then
    sqrtScan4Uint x (Contracts.bitOr r (shl 5 1)) z
  else
    sqrtScan4Uint x r z

private def sqrtScan6Contract (x r z : Uint256) : Contract Uint256 :=
  if 4722366482869645213695 < shr r x then
    let r := Contracts.bitOr r (shl 6 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtScan5Contract x r z
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtScan5Contract x r z

private def sqrtScan6Uint (x r z : Uint256) : Uint256 :=
  if 4722366482869645213695 < shr r x then
    sqrtScan5Uint x (Contracts.bitOr r (shl 6 1)) z
  else
    sqrtScan5Uint x r z

private def sqrtScanSourceUint (x : Uint256) : Uint256 :=
  let r : Uint256 := 0
  let r := if 87112285931760246646623899502532662132735 < x then shl 7 1 else r
  let r := if 4722366482869645213695 < shr r x then Contracts.bitOr r (shl 6 1) else r
  let r := if 1099511627775 < shr r x then Contracts.bitOr r (shl 5 1) else r
  if 16777215 < shr r x then Contracts.bitOr r (shl 4 1) else r

private def sqrtSourceContract (x : Uint256) : Contract Uint256 :=
  let z : Uint256 := 181
  let r : Uint256 := 0
  if 87112285931760246646623899502532662132735 < x then
    let r := shl 7 1
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtScan6Contract x r z
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => sqrtScan6Contract x r z

private def sqrtSourceUint (x : Uint256) : Uint256 :=
  let z : Uint256 := 181
  let r : Uint256 := 0
  if 87112285931760246646623899502532662132735 < x then
    sqrtScan6Uint x (shl 7 1) z
  else
    sqrtScan6Uint x r z

private theorem sqrtSourceUint_eq_finishScan (x : Uint256) :
    sqrtSourceUint x = sqrtFinishUint x (sqrtScanSourceUint x) 181 := by
  unfold sqrtSourceUint sqrtScanSourceUint sqrtScan6Uint sqrtScan5Uint sqrtScan4Uint
  by_cases h0 : 87112285931760246646623899502532662132735 < x
  · simp only [h0, if_true]
    by_cases h1 : 4722366482869645213695 < shr (shl 7 1) x
    · simp only [h1, if_true]
      by_cases h2 :
          1099511627775 < shr (Contracts.bitOr (shl 7 1) (shl 6 1)) x
      · simp only [h2, if_true]
        by_cases h3 :
            16777215 <
              shr (Contracts.bitOr (Contracts.bitOr (shl 7 1) (shl 6 1)) (shl 5 1)) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
      · simp only [h2, if_false]
        by_cases h3 : 16777215 < shr (Contracts.bitOr (shl 7 1) (shl 6 1)) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
    · simp only [h1, if_false]
      by_cases h2 : 1099511627775 < shr (shl 7 1) x
      · simp only [h2, if_true]
        by_cases h3 : 16777215 < shr (Contracts.bitOr (shl 7 1) (shl 5 1)) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
      · simp only [h2, if_false]
        by_cases h3 : 16777215 < shr (shl 7 1) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
  · simp only [h0, if_false]
    by_cases h1 : 4722366482869645213695 < shr 0 x
    · simp only [h1, if_true]
      by_cases h2 : 1099511627775 < shr (Contracts.bitOr 0 (shl 6 1)) x
      · simp only [h2, if_true]
        by_cases h3 :
            16777215 < shr (Contracts.bitOr (Contracts.bitOr 0 (shl 6 1)) (shl 5 1)) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
      · simp only [h2, if_false]
        by_cases h3 : 16777215 < shr (Contracts.bitOr 0 (shl 6 1)) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
    · simp only [h1, if_false]
      by_cases h2 : 1099511627775 < shr 0 x
      · simp only [h2, if_true]
        by_cases h3 : 16777215 < shr (Contracts.bitOr 0 (shl 5 1)) x
        · simp only [h3, if_true]
        · simp only [h3, if_false]
      · simp only [h2, if_false]
        by_cases h3 : 16777215 < shr 0 x
        · simp only [h3, if_true]
        · simp only [h3, if_false]

@[simp] private theorem sqrtThreshold136_val :
    (87112285931760246646623899502532662132735 : Uint256).val = 2 ^ 136 - 1 := by
  native_decide

@[simp] private theorem sqrtThreshold72_val :
    (4722366482869645213695 : Uint256).val = 2 ^ 72 - 1 := by
  native_decide

@[simp] private theorem sqrtThreshold40_val :
    (1099511627775 : Uint256).val = 2 ^ 40 - 1 := by
  native_decide

@[simp] private theorem sqrtThreshold24_val :
    (16777215 : Uint256).val = 2 ^ 24 - 1 := by
  native_decide

@[simp] private theorem shl_7_1_val : (shl 7 1).val = 128 := by
  native_decide

@[simp] private theorem shl_6_1_val : (shl 6 1).val = 64 := by
  native_decide

@[simp] private theorem shl_5_1_val : (shl 5 1).val = 32 := by
  native_decide

@[simp] private theorem shl_4_1_val : (shl 4 1).val = 16 := by
  native_decide

@[simp] private theorem bitOr_0_shl_6_1_val :
    (Contracts.bitOr 0 (shl 6 1)).val = 64 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_6_1_val :
    (Contracts.bitOr (shl 7 1) (shl 6 1)).val = 192 := by
  native_decide

@[simp] private theorem bitOr_0_shl_5_1_val :
    (Contracts.bitOr 0 (shl 5 1)).val = 32 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_5_1_val :
    (Contracts.bitOr (shl 7 1) (shl 5 1)).val = 160 := by
  native_decide

@[simp] private theorem bitOr_shl_6_1_shl_5_1_val :
    (Contracts.bitOr (shl 6 1) (shl 5 1)).val = 96 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_6_1_shl_5_1_val :
    (Contracts.bitOr (Contracts.bitOr (shl 7 1) (shl 6 1)) (shl 5 1)).val =
      224 := by
  native_decide

@[simp] private theorem bitOr_0_shl_4_1_val :
    (Contracts.bitOr 0 (shl 4 1)).val = 16 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_4_1_val :
    (Contracts.bitOr (shl 7 1) (shl 4 1)).val = 144 := by
  native_decide

@[simp] private theorem bitOr_shl_6_1_shl_4_1_val :
    (Contracts.bitOr (shl 6 1) (shl 4 1)).val = 80 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_6_1_shl_4_1_val :
    (Contracts.bitOr (Contracts.bitOr (shl 7 1) (shl 6 1)) (shl 4 1)).val =
      208 := by
  native_decide

@[simp] private theorem bitOr_shl_5_1_shl_4_1_val :
    (Contracts.bitOr (shl 5 1) (shl 4 1)).val = 48 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_5_1_shl_4_1_val :
    (Contracts.bitOr (Contracts.bitOr (shl 7 1) (shl 5 1)) (shl 4 1)).val =
      176 := by
  native_decide

@[simp] private theorem bitOr_shl_6_1_shl_5_1_shl_4_1_val :
    (Contracts.bitOr (Contracts.bitOr (shl 6 1) (shl 5 1)) (shl 4 1)).val =
      112 := by
  native_decide

@[simp] private theorem bitOr_shl_7_1_shl_6_1_shl_5_1_shl_4_1_val :
    (Contracts.bitOr
      (Contracts.bitOr (Contracts.bitOr (shl 7 1) (shl 6 1)) (shl 5 1))
      (shl 4 1)).val = 240 := by
  native_decide

private theorem sqrtScanStepUint_val
    (x r shiftWord thresholdWord : Uint256) (rn shift : Nat)
    (hr : r.val = rn)
    (hThreshold : thresholdWord.val = 2 ^ (shift + 8) - 1)
    (hOr : (Contracts.bitOr r shiftWord).val = rn + shift) :
    (if thresholdWord < shr r x then Contracts.bitOr r shiftWord else r).val =
      sqrtScanStepNat x.val rn shift := by
  unfold sqrtScanStepNat
  have hBranch :
      (thresholdWord < shr r x) ↔
        2 ^ (shift + 8) - 1 < x.val / 2 ^ rn := by
    change thresholdWord.val < (shr r x).val ↔
      2 ^ (shift + 8) - 1 < x.val / 2 ^ rn
    rw [shr_val, hr, hThreshold]
  by_cases h : 2 ^ (shift + 8) - 1 < x.val / 2 ^ rn
  · have hUint := hBranch.mpr h
    rw [if_pos hUint, if_pos h]
    exact hOr
  · have hUint : ¬ thresholdWord < shr r x := fun hh => h (hBranch.mp hh)
    rw [if_neg hUint, if_neg h]
    exact hr

private theorem bitOr_shl_6_1_sqrtScan_val
    (r : Uint256) {rn : Nat} (hr : r.val = rn)
    (hrn : rn = 0 ∨ rn = 128) :
    (Contracts.bitOr r (shl 6 1)).val = rn + 64 := by
  rcases hrn with rfl | rfl <;>
    simp [bitOr_val, hr, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] <;>
    native_decide

private theorem bitOr_shl_5_1_sqrtScan_val
    (r : Uint256) {rn : Nat} (hr : r.val = rn)
    (hrn : rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192) :
    (Contracts.bitOr r (shl 5 1)).val = rn + 32 := by
  rcases hrn with rfl | rfl | rfl | rfl <;>
    simp [bitOr_val, hr, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] <;>
    native_decide

private theorem bitOr_shl_4_1_sqrtScan_val
    (r : Uint256) {rn : Nat} (hr : r.val = rn)
    (hrn :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224) :
    (Contracts.bitOr r (shl 4 1)).val = rn + 16 := by
  rcases hrn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [bitOr_val, hr, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] <;>
    native_decide

private theorem sqrtScanStepNat_128_possible (x : Nat) :
    sqrtScanStepNat x 0 128 = 0 ∨ sqrtScanStepNat x 0 128 = 128 := by
  unfold sqrtScanStepNat
  by_cases h : 2 ^ (128 + 8) - 1 < x / 2 ^ 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

private theorem sqrtScanStepNat_64_possible
    (x rn : Nat) (hrn : rn = 0 ∨ rn = 128) :
    sqrtScanStepNat x rn 64 = 0 ∨ sqrtScanStepNat x rn 64 = 128 ∨
      sqrtScanStepNat x rn 64 = 64 ∨ sqrtScanStepNat x rn 64 = 192 := by
  unfold sqrtScanStepNat
  rcases hrn with rfl | rfl
  · by_cases h : 2 ^ (64 + 8) - 1 < x / 2 ^ 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega
  · by_cases h : 2 ^ (64 + 8) - 1 < x / 2 ^ 128
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega

private theorem sqrtScanStepNat_32_possible
    (x rn : Nat)
    (hrn : rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192) :
    sqrtScanStepNat x rn 32 = 0 ∨ sqrtScanStepNat x rn 32 = 128 ∨
      sqrtScanStepNat x rn 32 = 64 ∨ sqrtScanStepNat x rn 32 = 192 ∨
        sqrtScanStepNat x rn 32 = 32 ∨ sqrtScanStepNat x rn 32 = 160 ∨
          sqrtScanStepNat x rn 32 = 96 ∨ sqrtScanStepNat x rn 32 = 224 := by
  unfold sqrtScanStepNat
  rcases hrn with rfl | rfl | rfl | rfl
  · by_cases h : 2 ^ (32 + 8) - 1 < x / 2 ^ 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega
  · by_cases h : 2 ^ (32 + 8) - 1 < x / 2 ^ 128
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega
  · by_cases h : 2 ^ (32 + 8) - 1 < x / 2 ^ 64
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega
  · by_cases h : 2 ^ (32 + 8) - 1 < x / 2 ^ 192
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega

private theorem sqrtScanStepNat_16_le_240
    (x rn : Nat)
    (hrn :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224) :
    sqrtScanStepNat x rn 16 ≤ 240 := by
  unfold sqrtScanStepNat
  rcases hrn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    split <;> norm_num

private theorem sqrtScanNat_le_240 (x : Nat) :
    sqrtScanNat x ≤ 240 := by
  let r1 := sqrtScanStepNat x 0 128
  have hr1 : r1 = 0 ∨ r1 = 128 := by
    simpa [r1] using sqrtScanStepNat_128_possible x
  let r2 := sqrtScanStepNat x r1 64
  have hr2 : r2 = 0 ∨ r2 = 128 ∨ r2 = 64 ∨ r2 = 192 := by
    simpa [r2] using sqrtScanStepNat_64_possible x r1 hr1
  let r3 := sqrtScanStepNat x r2 32
  have hr3 :
      r3 = 0 ∨ r3 = 128 ∨ r3 = 64 ∨ r3 = 192 ∨
        r3 = 32 ∨ r3 = 160 ∨ r3 = 96 ∨ r3 = 224 := by
    simpa [r3] using sqrtScanStepNat_32_possible x r2 hr2
  simpa [sqrtScanNat, r1, r2, r3] using sqrtScanStepNat_16_le_240 x r3 hr3

private theorem sqrtScanSourceUint_val (x : Uint256) :
    (sqrtScanSourceUint x).val = sqrtScanNat x.val := by
  unfold sqrtScanSourceUint sqrtScanNat
  let ru1 : Uint256 :=
    if 87112285931760246646623899502532662132735 < x then shl 7 1 else 0
  let rn1 : Nat := sqrtScanStepNat x.val 0 128
  have hru1 : ru1.val = rn1 := by
    dsimp [ru1, rn1, sqrtScanStepNat]
    have hBranch :
        (87112285931760246646623899502532662132735 < x) ↔
          2 ^ (128 + 8) - 1 < x.val / 2 ^ 0 := by
      change (87112285931760246646623899502532662132735 : Uint256).val < x.val ↔
        2 ^ (128 + 8) - 1 < x.val / 2 ^ 0
      rw [sqrtThreshold136_val]
      norm_num
    by_cases h : 2 ^ (128 + 8) - 1 < x.val / 2 ^ 0
    · have hUint := hBranch.mpr h
      have hUintVal :
          (87112285931760246646623899502532662132735 : Uint256).val < x.val := hUint
      have hNat : 87112285931760246646623899502532662132735 < x.val / 1 := by
        simpa using h
      rw [if_pos hUintVal, if_pos hNat]
      exact shl_7_1_val
    · have hUint : ¬ 87112285931760246646623899502532662132735 < x :=
        fun hh => h (hBranch.mp hh)
      have hUintVal :
          ¬ (87112285931760246646623899502532662132735 : Uint256).val < x.val := hUint
      have hNat : ¬ 87112285931760246646623899502532662132735 < x.val / 1 := by
        simpa using h
      rw [if_neg hUintVal, if_neg hNat]
      rfl
  let ru2 : Uint256 :=
    if 4722366482869645213695 < shr ru1 x then
      Contracts.bitOr ru1 (shl 6 1)
    else
      ru1
  let rn2 : Nat := sqrtScanStepNat x.val rn1 64
  have hrn1 : rn1 = 0 ∨ rn1 = 128 := by
    simpa [rn1] using sqrtScanStepNat_128_possible x.val
  have hOr2 : (Contracts.bitOr ru1 (shl 6 1)).val = rn1 + 64 := by
    exact bitOr_shl_6_1_sqrtScan_val ru1 hru1 hrn1
  have hru2 : ru2.val = rn2 := by
    dsimp [ru2, rn2]
    exact sqrtScanStepUint_val x ru1 (shl 6 1) 4722366482869645213695 rn1 64
      hru1 (by norm_num) hOr2
  let ru3 : Uint256 :=
    if 1099511627775 < shr ru2 x then
      Contracts.bitOr ru2 (shl 5 1)
    else
      ru2
  let rn3 : Nat := sqrtScanStepNat x.val rn2 32
  have hrn2 : rn2 = 0 ∨ rn2 = 128 ∨ rn2 = 64 ∨ rn2 = 192 := by
    simpa [rn2] using sqrtScanStepNat_64_possible x.val rn1 hrn1
  have hOr3 : (Contracts.bitOr ru2 (shl 5 1)).val = rn2 + 32 := by
    exact bitOr_shl_5_1_sqrtScan_val ru2 hru2 hrn2
  have hru3 : ru3.val = rn3 := by
    dsimp [ru3, rn3]
    exact sqrtScanStepUint_val x ru2 (shl 5 1) 1099511627775 rn2 32
      hru2 (by norm_num) hOr3
  let ru4 : Uint256 :=
    if 16777215 < shr ru3 x then
      Contracts.bitOr ru3 (shl 4 1)
    else
      ru3
  let rn4 : Nat := sqrtScanStepNat x.val rn3 16
  have hrn3 :
      rn3 = 0 ∨ rn3 = 128 ∨ rn3 = 64 ∨ rn3 = 192 ∨
        rn3 = 32 ∨ rn3 = 160 ∨ rn3 = 96 ∨ rn3 = 224 := by
    simpa [rn3] using sqrtScanStepNat_32_possible x.val rn2 hrn2
  have hOr4 : (Contracts.bitOr ru3 (shl 4 1)).val = rn3 + 16 := by
    exact bitOr_shl_4_1_sqrtScan_val ru3 hru3 hrn3
  have hru4 : ru4.val = rn4 := by
    dsimp [ru4, rn4]
    exact sqrtScanStepUint_val x ru3 (shl 4 1) 16777215 rn3 16
      hru3 (by norm_num) hOr4
  change ru4.val = rn4
  exact hru4

private theorem uint181_val : (181 : Uint256).val = 181 := by
  native_decide

private theorem uint65536_val : (65536 : Uint256).val = 65536 := by
  native_decide

private theorem uint18_val : (18 : Uint256).val = 18 := by
  native_decide

private theorem shl_small_val (shift value : Uint256)
    (h : value.val * 2 ^ shift.val < Verity.Core.Uint256.modulus) :
    (shl shift value).val = value.val * 2 ^ shift.val := by
  rw [shl_val]
  exact Nat.mod_eq_of_lt h

private theorem add_uint65536_val (a : Uint256)
    (h : a.val + 65536 < Verity.Core.Uint256.modulus) :
    (add a 65536).val = a.val + 65536 := by
  have hAddLt : a.val + (65536 : Uint256).val < Verity.Core.Uint256.modulus := by
    simpa [uint65536_val] using h
  simpa [HAdd.hAdd, add, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    uint65536_val] using Verity.Core.Uint256.add_eq_of_lt
      (a := a) (b := (65536 : Uint256)) hAddLt

private theorem mul_val_of_lt (a b : Uint256)
    (h : a.val * b.val < Verity.Core.Uint256.modulus) :
    (mul a b).val = a.val * b.val := by
  simpa [HMul.hMul] using Verity.Core.Uint256.mul_eq_of_lt (a := a) (b := b) h

private theorem add_val_of_lt (a b : Uint256)
    (h : a.val + b.val < Verity.Core.Uint256.modulus) :
    (add a b).val = a.val + b.val := by
  simpa [HAdd.hAdd] using Verity.Core.Uint256.add_eq_of_lt (a := a) (b := b) h

private theorem nat_sqrt_lt_pow128 {x : Nat} (hxLt : x < 2 ^ 256) :
    Nat.sqrt x < 2 ^ 128 := by
  by_contra h
  have hLe : 2 ^ 128 ≤ Nat.sqrt x := Nat.le_of_not_gt h
  have hSqLe : (2 ^ 128) * (2 ^ 128) ≤ Nat.sqrt x * Nat.sqrt x :=
    Nat.mul_le_mul hLe hLe
  have hSqrtLe : Nat.sqrt x * Nat.sqrt x ≤ x := Nat.sqrt_le x
  have hPow : (2 ^ 128 : Nat) * 2 ^ 128 = 2 ^ 256 := by
    rw [← Nat.pow_add]
  omega

private theorem nat_sqrt_pos_of_ge_256 {x : Nat} (hx : 2 ^ 8 ≤ x) :
    0 < Nat.sqrt x := by
  have h : 1 * 1 ≤ x := by omega
  exact (Nat.le_sqrt).2 h

private theorem div_le_sqrt_add_two
    (x z : Nat) (haPos : 0 < Nat.sqrt x) (hFloor : Nat.sqrt x ≤ z) :
    x / z ≤ Nat.sqrt x + 2 := by
  let a := Nat.sqrt x
  have hzPos : 0 < z := lt_of_lt_of_le (by simpa [a] using haPos) hFloor
  have hDivMono : x / z ≤ x / a := by
    exact Nat.div_le_div_left hFloor (by simpa [a] using haPos)
  have hMulLt : x < a * (a + 3) := by
    have hSqrt := Nat.lt_succ_sqrt x
    nlinarith [hSqrt]
  have hDivLt : x / a < a + 3 := by
    exact (Nat.div_lt_iff_lt_mul (by simpa [a] using haPos)).2
      (by simpa [Nat.mul_comm] using hMulLt)
  have hDivLe : x / a ≤ a + 2 := by omega
  exact le_trans hDivMono (by simpa [a] using hDivLe)

private theorem sqrtStepNat_add_no_overflow
    (x z : Nat) (hxLt : x < 2 ^ 256) (haPos : 0 < Nat.sqrt x)
    (hFloor : Nat.sqrt x ≤ z) (hUpper : z ≤ 3 * 2 ^ 128) :
    z + x / z < Verity.Core.Uint256.modulus := by
  have hDivLe := div_le_sqrt_add_two x z haPos hFloor
  have hSqrtLt := nat_sqrt_lt_pow128 (x := x) hxLt
  have hSumLe : z + x / z ≤ 4 * 2 ^ 128 + 2 := by
    omega
  have hBound : 4 * 2 ^ 128 + 2 < Verity.Core.Uint256.modulus := by
    native_decide
  exact lt_of_le_of_lt hSumLe hBound

private theorem sqrtStepNat_le_three_pow128
    (x z : Nat) (hxLt : x < 2 ^ 256) (haPos : 0 < Nat.sqrt x)
    (hFloor : Nat.sqrt x ≤ z) (hUpper : z ≤ 3 * 2 ^ 128) :
    sqrtStepNat x z ≤ 3 * 2 ^ 128 := by
  unfold sqrtStepNat
  have hDivLe := div_le_sqrt_add_two x z haPos hFloor
  have hSqrtLt := nat_sqrt_lt_pow128 (x := x) hxLt
  have hNum : z + x / z ≤ 4 * 2 ^ 128 + 2 := by omega
  have hDiv : (z + x / z) / 2 ≤ (4 * 2 ^ 128 + 2) / 2 :=
    Nat.div_le_div_right hNum
  have hBound : (4 * 2 ^ 128 + 2) / 2 ≤ 3 * 2 ^ 128 := by
    native_decide
  exact le_trans hDiv hBound

private theorem sqrtSeedNat_add_no_overflow
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    soladySqrtSeedNat x + x / soladySqrtSeedNat x <
      Verity.Core.Uint256.modulus := by
  let z := soladySqrtSeedNat x
  let α := Real.sqrt (x : ℝ)
  have hSeed := soladySqrtSeedNat_real_bounds x hx hxLt
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hαPos : 0 < α := by
    simpa [α] using Real.sqrt_pos.2 (Nat.cast_pos.2 hxPos)
  have hαLt : α < (2 : ℝ) ^ 128 := by
    have hxLtR : (x : ℝ) < (2 : ℝ) ^ 256 := by exact_mod_cast hxLt
    have hPowEq : ((2 : ℝ) ^ 128) ^ 2 = (2 : ℝ) ^ 256 := by
      rw [sq, ← pow_add]
    rw [Real.sqrt_lt' (by positivity : 0 < (2 : ℝ) ^ 128)]
    rw [hPowEq]
    exact hxLtR
  have hzPos : 0 < z := by simpa [z] using hSeed.1
  have hzUpperR : (z : ℝ) < 3 * (2 : ℝ) ^ 128 := by
    have h : (z : ℝ) ≤ ((23 : ℝ) / 8) * α := by
      have hRatio := hSeed.2.2
      rw [div_le_iff₀ hαPos] at hRatio
      simpa [z, α] using hRatio
    nlinarith
  have hzUpper : z < 3 * 2 ^ 128 := by exact_mod_cast hzUpperR
  have hDivUpperR : ((x / z : Nat) : ℝ) < 3 * (2 : ℝ) ^ 128 := by
    have hDivCast : ((x / z : Nat) : ℝ) ≤ (x : ℝ) / (z : ℝ) := Nat.cast_div_le
    have hzLower : ((8 : ℝ) / 23) * α ≤ (z : ℝ) := by
      have hRatio := hSeed.2.1
      rw [le_div_iff₀ hαPos] at hRatio
      simpa [z, α] using hRatio
    have hzPosR : 0 < (z : ℝ) := Nat.cast_pos.2 hzPos
    have hDivReal : (x : ℝ) / (z : ℝ) ≤ ((23 : ℝ) / 8) * α := by
      have hαSq : α ^ 2 = (x : ℝ) := by
        simp [α, Real.sq_sqrt (le_of_lt (Nat.cast_pos.2 hxPos))]
      rw [← hαSq]
      rw [div_le_iff₀ hzPosR]
      nlinarith
    exact lt_of_le_of_lt (le_trans hDivCast hDivReal) (by nlinarith)
  have hDivUpper : x / z < 3 * 2 ^ 128 := by exact_mod_cast hDivUpperR
  have hSum : z + x / z < 6 * 2 ^ 128 := by omega
  have hBound : 6 * 2 ^ 128 < Verity.Core.Uint256.modulus := by
    native_decide
  exact lt_trans hSum hBound

private theorem sqrtFinishSeedUint_val_large
    (x : Uint256) (hx : 2 ^ 8 ≤ x.val) :
    (sqrtFinishSeedUint x (sqrtScanSourceUint x) 181).val =
      soladySqrtSeedNat x.val := by
  let rU := sqrtScanSourceUint x
  let r := sqrtScanNat x.val
  have hR : rU.val = r := by
    simpa [rU, r] using sqrtScanSourceUint_val x
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hrLe : r ≤ 240 := by
    simpa [r] using sqrtScanNat_le_240 x.val
  have hrHalfLe : r / 2 ≤ 120 := by
    have hTwo : 2 * (r / 2) ≤ r := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self r 2
    omega
  have hShiftVal : (shr 1 rU).val = r / 2 := by
    rw [shr_val, hR]
    norm_num
  have hShlLt : (181 : Uint256).val * 2 ^ (shr 1 rU).val <
      Verity.Core.Uint256.modulus := by
    rw [uint181_val, hShiftVal]
    have hPow : 2 ^ (r / 2) ≤ 2 ^ 120 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrHalfLe
    have hBound : 181 * 2 ^ 120 < Verity.Core.Uint256.modulus := by
      native_decide
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 181 hPow) hBound
  have hScaledVal : (shl (shr 1 rU) 181).val = 181 * 2 ^ (r / 2) := by
    rw [shl_small_val _ _ hShlLt, uint181_val, hShiftVal]
  have hShrXVal : (shr rU x).val = x.val / 2 ^ r := by
    rw [shr_val, hR]
  have hyUpper : x.val / 2 ^ r < 2 ^ 24 := by
    simpa [r] using sqrtScanNat_upper_bound x.val hx hxLt
  have hAddLt : (shr rU x).val + 65536 < Verity.Core.Uint256.modulus := by
    rw [hShrXVal]
    have hSmall : x.val / 2 ^ r + 65536 < 2 ^ 25 := by
      norm_num
      omega
    exact lt_of_lt_of_le hSmall (by native_decide)
  have hAddVal : (add (shr rU x) 65536).val = x.val / 2 ^ r + 65536 := by
    rw [add_uint65536_val (shr rU x) hAddLt, hShrXVal]
  have hMulLt :
      (shl (shr 1 rU) 181).val * (add (shr rU x) 65536).val <
        Verity.Core.Uint256.modulus := by
    rw [hScaledVal, hAddVal]
    have hPow : 2 ^ (r / 2) ≤ 2 ^ 120 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrHalfLe
    have hScaledLe : 181 * 2 ^ (r / 2) ≤ 181 * 2 ^ 120 :=
      Nat.mul_le_mul_left 181 hPow
    have hAddLe : x.val / 2 ^ r + 65536 ≤ 2 ^ 25 := by omega
    have hProductLe :
        (181 * 2 ^ (r / 2)) * (x.val / 2 ^ r + 65536) ≤
          (181 * 2 ^ 120) * 2 ^ 25 :=
      Nat.mul_le_mul hScaledLe hAddLe
    have hBound : (181 * 2 ^ 120) * 2 ^ 25 < Verity.Core.Uint256.modulus := by
      native_decide
    exact lt_of_le_of_lt hProductLe hBound
  have hMulVal :
      (mul (shl (shr 1 rU) 181) (add (shr rU x) 65536)).val =
        (181 * 2 ^ (r / 2)) * (x.val / 2 ^ r + 65536) := by
    rw [mul_val_of_lt _ _ hMulLt, hScaledVal, hAddVal]
  unfold sqrtFinishSeedUint soladySqrtSeedNat
  simp only [rU, r]
  rw [shr_val, hMulVal, uint18_val]

private theorem sqrtStepUint_val
    (x zU : Uint256) (z : Nat)
    (hzVal : zU.val = z) (hzPos : 0 < z)
    (hAddLt : z + x.val / z < Verity.Core.Uint256.modulus) :
    (shr 1 (add zU (div x zU))).val = sqrtStepNat x.val z := by
  have hzUNe : zU.val ≠ 0 := by omega
  have hDivVal : (div x zU).val = x.val / z := by
    rw [div_val x zU hzUNe, hzVal]
  have hAddLtU : zU.val + (div x zU).val < Verity.Core.Uint256.modulus := by
    simpa [hzVal, hDivVal] using hAddLt
  have hAddVal : (add zU (div x zU)).val = z + x.val / z := by
    rw [add_val_of_lt _ _ hAddLtU, hzVal, hDivVal]
  unfold sqrtStepNat
  rw [shr_val, hAddVal]
  norm_num

private theorem sqrtIterUint_val_of_nat_floor
    (steps : Nat) (x zU : Uint256) (z : Nat)
    (hxLt : x.val < 2 ^ 256) (haPos : 0 < Nat.sqrt x.val)
    (hzVal : zU.val = z)
    (hFloor : Nat.sqrt x.val ≤ z) (hUpper : z ≤ 3 * 2 ^ 128) :
    (sqrtIterUint steps x zU).val = sqrtIterNat steps x.val z := by
  induction steps generalizing zU z with
  | zero =>
      simpa [sqrtIterUint, sqrtIterNat] using hzVal
  | succ steps ih =>
      have hzPos : 0 < z := lt_of_lt_of_le haPos hFloor
      have hAddLt := sqrtStepNat_add_no_overflow x.val z hxLt haPos hFloor hUpper
      have hStepVal :
          (shr 1 (add zU (div x zU))).val = sqrtStepNat x.val z :=
        sqrtStepUint_val x zU z hzVal hzPos hAddLt
      have hNextFloor : Nat.sqrt x.val ≤ sqrtStepNat x.val z :=
        sqrtStepNat_ge_floor x.val z hzPos
      have hNextUpper : sqrtStepNat x.val z ≤ 3 * 2 ^ 128 :=
        sqrtStepNat_le_three_pow128 x.val z hxLt haPos hFloor hUpper
      have hTail := ih (shr 1 (add zU (div x zU))) (sqrtStepNat x.val z)
        hStepVal hNextFloor hNextUpper
      simpa [sqrtIterUint, sqrtIterNat] using hTail

private theorem sqrtBeforeCorrectionUint_val_large
    (x : Uint256) (hx : 2 ^ 8 ≤ x.val) :
    (sqrtBeforeCorrectionUint x (sqrtScanSourceUint x) 181).val =
      soladySqrtBeforeCorrectionNat x.val := by
  let seedU := sqrtFinishSeedUint x (sqrtScanSourceUint x) 181
  let seed := soladySqrtSeedNat x.val
  let z1 := sqrtStepNat x.val seed
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hxPos : 0 < x.val := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hSqrtPos : 0 < Nat.sqrt x.val := nat_sqrt_pos_of_ge_256 hx
  have hSeedVal : seedU.val = seed := by
    simpa [seedU, seed] using sqrtFinishSeedUint_val_large x hx
  have hSeedInfo := soladySqrtSeedNat_real_bounds x.val hx hxLt
  have hSeedPos : 0 < seed := by simpa [seed] using hSeedInfo.1
  have hSeedAddLt : seed + x.val / seed < Verity.Core.Uint256.modulus := by
    simpa [seed] using sqrtSeedNat_add_no_overflow x.val hx hxLt
  have hStepVal :
      (shr 1 (add seedU (div x seedU))).val = z1 := by
    simpa [z1] using sqrtStepUint_val x seedU seed hSeedVal hSeedPos hSeedAddLt
  have hZ1Floor : Nat.sqrt x.val ≤ z1 := by
    simpa [z1] using sqrtStepNat_ge_floor x.val seed hSeedPos
  have hZ1Upper : z1 ≤ 3 * 2 ^ 128 := by
    let α := Real.sqrt (x.val : ℝ)
    have hxPosR : 0 < (x.val : ℝ) := Nat.cast_pos.2 hxPos
    have hαPos : 0 < α := by
      simpa [α] using Real.sqrt_pos.2 hxPosR
    have hStepUpperRaw := sqrtStepNat_real_ratio_upper
      (x := x.val) (z := seed) hxPos hSeedPos (u := (23 : ℝ) / 8)
      (by norm_num)
      (by simpa [seed, α] using hSeedInfo.2.1)
      (by simpa [seed, α] using hSeedInfo.2.2)
    have hαLt : α < (2 : ℝ) ^ 128 := by
      have hxLtR : (x.val : ℝ) < (2 : ℝ) ^ 256 := by exact_mod_cast hxLt
      have hPowEq : ((2 : ℝ) ^ 128) ^ 2 = (2 : ℝ) ^ 256 := by
        rw [sq, ← pow_add]
      rw [Real.sqrt_lt' (by positivity : 0 < (2 : ℝ) ^ 128)]
      rw [hPowEq]
      exact hxLtR
    have hZ1R : (z1 : ℝ) < 3 * (2 : ℝ) ^ 128 := by
      have h : (z1 : ℝ) ≤ (((23 : ℝ) / 8 + 1 / ((23 : ℝ) / 8)) / 2) * α := by
        simpa [z1, sqrtNewtonBoundRat] using hStepUpperRaw
      nlinarith
    exact le_of_lt (by exact_mod_cast hZ1R)
  have hTail := sqrtIterUint_val_of_nat_floor 6 x (shr 1 (add seedU (div x seedU))) z1
    hxLt hSqrtPos hStepVal hZ1Floor hZ1Upper
  unfold sqrtBeforeCorrectionUint soladySqrtBeforeCorrectionNat sqrtIterUint sqrtIterNat
  simpa [seedU, seed, z1] using hTail

private theorem sqrtFinishCorrectionUint_val
    (x zU : Uint256) (z : Nat)
    (hZVal : zU.val = z) (hzPos : 0 < z) :
    (if div x zU < zU then sub zU 1 else zU).val =
      sqrtCorrectNat x.val z := by
  have hzUNe : zU.val ≠ 0 := by omega
  have hDivVal : (div x zU).val = x.val / z := by
    rw [div_val x zU hzUNe, hZVal]
  have hBranchIff : (div x zU < zU) ↔ x.val / z < z := by
    change (div x zU).val < zU.val ↔ x.val / z < z
    rw [hDivVal, hZVal]
  unfold sqrtCorrectNat
  by_cases h : x.val / z < z
  · have hUint := hBranchIff.mpr h
    rw [if_pos hUint, if_pos h]
    have hOne : (1 : Uint256).val = 1 := by simp
    have hSub : (sub zU 1).val = z - 1 := by
      have hLe : (1 : Uint256).val ≤ zU.val := by
        rw [hOne, hZVal]
        exact hzPos
      simpa [hZVal, hOne, HSub.hSub] using
        Verity.Core.Uint256.sub_eq_of_le (a := zU) (b := (1 : Uint256)) hLe
    exact hSub
  · have hUint : ¬ div x zU < zU := fun hh => h (hBranchIff.mp hh)
    rw [if_neg hUint, if_neg h]
    exact hZVal

private theorem sqrtFinishUint_val_large
    (x : Uint256) (hx : 2 ^ 8 ≤ x.val) :
    (sqrtFinishUint x (sqrtScanSourceUint x) 181).val =
      soladySqrtNat x.val := by
  have hZVal :
      (sqrtBeforeCorrectionUint x (sqrtScanSourceUint x) 181).val =
        soladySqrtBeforeCorrectionNat x.val :=
    sqrtBeforeCorrectionUint_val_large x hx
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hNear := soladySqrtBeforeCorrectionNat_near_floor x.val hx hxLt
  have hzPos : 0 < soladySqrtBeforeCorrectionNat x.val := by
    have hSqrtPos : 0 < Nat.sqrt x.val := nat_sqrt_pos_of_ge_256 hx
    exact lt_of_lt_of_le hSqrtPos hNear.1
  simpa [sqrtFinishUint, soladySqrtNat] using
    sqrtFinishCorrectionUint_val x
      (sqrtBeforeCorrectionUint x (sqrtScanSourceUint x) 181)
      (soladySqrtBeforeCorrectionNat x.val) hZVal hzPos

private theorem sqrtFinishIf_run_eq_uint (x z : Uint256) (s : ContractState) :
    ((if div x z < z then Verity.pure (sub z 1) else Verity.pure z).run s).fst =
      if div x z < z then sub z 1 else z := by
  by_cases h : div x z < z
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

private theorem sqrtFinishContract_run_eq_uint
    (x r z : Uint256) (s : ContractState) :
    ((sqrtFinishContract x r z).run s).fst = sqrtFinishUint x r z := by
  unfold sqrtFinishContract sqrtFinishUint
  exact sqrtFinishIf_run_eq_uint x (sqrtBeforeCorrectionUint x r z) s

private theorem sqrtScan4Contract_run_eq_uint
    (x r z : Uint256) (s : ContractState) :
    ((sqrtScan4Contract x r z).run s).fst = sqrtScan4Uint x r z := by
  unfold sqrtScan4Contract sqrtScan4Uint
  by_cases h : 16777215 < shr r x
  · simp only [h, if_true, bind_pure_contract, sqrtFinishContract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, sqrtFinishContract_run_eq_uint]

private theorem sqrtScan5Contract_run_eq_uint
    (x r z : Uint256) (s : ContractState) :
    ((sqrtScan5Contract x r z).run s).fst = sqrtScan5Uint x r z := by
  unfold sqrtScan5Contract sqrtScan5Uint
  by_cases h : 1099511627775 < shr r x
  · simp only [h, if_true, bind_pure_contract, sqrtScan4Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, sqrtScan4Contract_run_eq_uint]

private theorem sqrtScan6Contract_run_eq_uint
    (x r z : Uint256) (s : ContractState) :
    ((sqrtScan6Contract x r z).run s).fst = sqrtScan6Uint x r z := by
  unfold sqrtScan6Contract sqrtScan6Uint
  by_cases h : 4722366482869645213695 < shr r x
  · simp only [h, if_true, bind_pure_contract, sqrtScan5Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, sqrtScan5Contract_run_eq_uint]

private theorem sqrtSourceContract_run_eq_uint (x : Uint256) (s : ContractState) :
    ((sqrtSourceContract x).run s).fst = sqrtSourceUint x := by
  unfold sqrtSourceContract sqrtSourceUint
  by_cases h : 87112285931760246646623899502532662132735 < x
  · simp only [h, if_true, bind_pure_contract, sqrtScan6Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, sqrtScan6Contract_run_eq_uint]

private theorem sqrt_run_eq_sourceUint (x : Uint256) (s : ContractState) :
    ((sqrt x).run s).fst = sqrtSourceUint x := by
  rw [sqrt, Tamago.Utils.FixedPointMathLibBase.sqrt.eq_1]
  unfold sqrtSourceUint
  by_cases h : 87112285931760246646623899502532662132735 < x
  · simp only [h, if_true, bind_pure_contract]
    change ((sqrtScan6Contract x (shl 7 1) 181).run s).fst =
      sqrtScan6Uint x (shl 7 1) 181
    exact sqrtScan6Contract_run_eq_uint x (shl 7 1) 181 s
  · simp only [h, if_false, bind_pure_contract]
    change ((sqrtScan6Contract x 0 181).run s).fst = sqrtScan6Uint x 0 181
    exact sqrtScan6Contract_run_eq_uint x 0 181 s

private theorem sqrtSourceUint_val_small :
    ∀ x : Fin 256,
      (sqrtSourceUint (uintOfNat x.val)).val = soladySqrtNat x.val := by
  native_decide

private theorem soladySqrt_run_eq_model (x : Uint256) (s : ContractState) :
    ((sqrt x).run s).fst.val = soladySqrtNat x.val := by
  rw [sqrt_run_eq_sourceUint x s]
  by_cases hxSmall : x.val < 256
  · have hxEq : x = uintOfNat x.val := by
      apply Verity.Core.Uint256.ext
      have hLt : x.val < Verity.Core.Uint256.modulus := x.isLt
      simp [uintOfNat_val_of_lt hLt]
    rw [hxEq]
    simpa [uintOfNat_val_of_lt x.isLt] using
      sqrtSourceUint_val_small ⟨x.val, hxSmall⟩
  · have hxLarge : 2 ^ 8 ≤ x.val := by
      norm_num at hxSmall
      omega
    simpa [sqrtSourceUint_eq_finishScan x] using sqrtFinishUint_val_large x hxLarge

theorem sqrt_returns_math_floor (x : Uint256) (s : ContractState) :
    sqrt_property x ((sqrt x).run s).fst := by
  unfold sqrt_property
  rw [soladySqrt_run_eq_model x s]
  exact soladySqrtNat_property x.val (by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt)

private def natCbrt (n : Nat) : Nat :=
  Nat.findGreatest (fun r => r ^ 3 ≤ n) n

private theorem nat_le_cube_of_pos {n : Nat} (hn : 0 < n) : n ≤ n ^ 3 := by
  have hsq : 1 ≤ n * n := Nat.succ_le_of_lt (Nat.mul_pos hn hn)
  calc
    n = n * 1 := by rw [Nat.mul_one]
    _ ≤ n * (n * n) := Nat.mul_le_mul_left n hsq
    _ = n ^ 3 := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc]

private theorem natCbrt_cube_le (n : Nat) :
    natCbrt n ^ 3 ≤ n := by
  unfold natCbrt
  exact Nat.findGreatest_spec
    (P := fun r => r ^ 3 ≤ n)
    (m := 0) (n := n)
    (Nat.zero_le _) (by norm_num)

private theorem natCbrt_next_cube_gt (n : Nat) :
    n < (natCbrt n + 1) ^ 3 := by
  by_contra h
  have hCube : (natCbrt n + 1) ^ 3 ≤ n := Nat.le_of_not_gt h
  have hBound : natCbrt n + 1 ≤ n := by
    exact Nat.le_trans (nat_le_cube_of_pos (Nat.succ_pos _)) hCube
  have hNot :
      ¬ (natCbrt n + 1) ^ 3 ≤ n := by
    exact Nat.findGreatest_is_greatest
      (P := fun r => r ^ 3 ≤ n)
      (n := n)
      (k := natCbrt n + 1)
      (Nat.lt_succ_self _) hBound
  exact hNot hCube

private theorem cbrt_near_floor_property
    (x z : Nat)
    (hLower : natCbrt x ≤ z)
    (hUpper : z ≤ natCbrt x + 1) :
    (z - 1) * (z - 1) * (z - 1) ≤ x ∧
      x < (z + 1) * (z + 1) * (z + 1) := by
  constructor
  · have hzPred : z - 1 ≤ natCbrt x := by omega
    have hCube :=
      Nat.mul_le_mul (Nat.mul_le_mul hzPred hzPred) hzPred
    exact le_trans hCube (by
      simpa [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc] using natCbrt_cube_le x)
  · have hSuccLe : natCbrt x + 1 ≤ z + 1 := by omega
    have hCube :=
      Nat.mul_le_mul (Nat.mul_le_mul hSuccLe hSuccLe) hSuccLe
    exact lt_of_lt_of_le (by
      simpa [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc] using natCbrt_next_cube_gt x) hCube

private def cbrtStepNat (x z : Nat) : Nat :=
  (x / (z * z) + z + z) / 3

private def cbrtIterNat : Nat → Nat → Nat → Nat
  | 0, _x, z => z
  | steps + 1, x, z => cbrtIterNat steps x (cbrtStepNat x z)

private def cbrtScanStepNat (x r shift : Nat) : Nat :=
  if 2 ^ shift - 1 < x / 2 ^ r then r + shift else r

private def cbrtScanNat (x : Nat) : Nat :=
  let r := cbrtScanStepNat x 0 128
  let r := cbrtScanStepNat x r 64
  let r := cbrtScanStepNat x r 32
  let r := cbrtScanStepNat x r 16
  cbrtScanStepNat x r 8

private def soladyCbrtSeedNat (x : Nat) : Nat :=
  let r := cbrtScanNat x
  let seedBase := if 15 < x / 2 ^ r then 30 else 15
  (seedBase * 2 ^ (r / 3)) / Nat.xor 7 (r % 3)

private def soladyCbrtBeforeCorrectionNat (x : Nat) : Nat :=
  cbrtIterNat 7 x (soladyCbrtSeedNat x)

private def soladyCbrtNat (x : Nat) : Nat :=
  cbrtCorrectNat x (soladyCbrtBeforeCorrectionNat x)

private theorem soladyCbrtNat_property_small :
    ∀ x : Fin 256,
      soladyCbrtNat x.val * soladyCbrtNat x.val * soladyCbrtNat x.val ≤ x.val ∧
        x.val < (soladyCbrtNat x.val + 1) * (soladyCbrtNat x.val + 1) *
          (soladyCbrtNat x.val + 1) := by
  native_decide

private theorem soladyCbrtNat_property_of_lt_256 (x : Nat) (hx : x < 256) :
    soladyCbrtNat x * soladyCbrtNat x * soladyCbrtNat x ≤ x ∧
      x < (soladyCbrtNat x + 1) * (soladyCbrtNat x + 1) *
        (soladyCbrtNat x + 1) := by
  simpa using soladyCbrtNat_property_small ⟨x, hx⟩

private theorem cbrtStepNat_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) :
    0 < cbrtStepNat x z := by
  unfold cbrtStepNat
  cases z with
  | zero => cases hz
  | succ z' =>
      cases z' with
      | zero =>
          have hDiv : x / (1 * 1) = x := by simp
          rw [hDiv]
          exact Nat.div_pos (by omega) (by decide : 0 < 3)
      | succ z'' =>
          have hBase : 3 ≤ Nat.succ (Nat.succ z'') + Nat.succ (Nat.succ z'') := by
            omega
          have hNum :
              3 ≤ x / (Nat.succ (Nat.succ z'') * Nat.succ (Nat.succ z'')) +
                Nat.succ (Nat.succ z'') + Nat.succ (Nat.succ z'') := by
            exact le_trans hBase
              (Nat.add_le_add_right
                (Nat.le_add_left (Nat.succ (Nat.succ z''))
                  (x / (Nat.succ (Nat.succ z'') * Nat.succ (Nat.succ z''))))
                (Nat.succ (Nat.succ z'')))
          exact Nat.div_pos hNum (by decide : 0 < 3)

private theorem cbrtStepNat_ge_floor (x z : Nat) (hz : 0 < z) :
    natCbrt x ≤ cbrtStepNat x z := by
  unfold cbrtStepNat
  let a := natCbrt x
  have ha3 : a * a * a ≤ x := by
    simpa [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc, a] using natCbrt_cube_le x
  have hzz : 0 < z * z := Nat.mul_pos hz hz
  have hsum : a * 3 ≤ x / (z * z) + z + z := by
    by_cases hzle : 2 * z ≤ 3 * a
    · have hmul : (3 * a - 2 * z) * (z * z) ≤ a * a * a := by
        have hmulInt :
            ((3 * a - 2 * z : Nat) : Int) * ((z * z : Nat) : Int) ≤
              (a : Int) * (a : Int) * (a : Int) := by
          have hcast :
              ((3 * a - 2 * z : Nat) : Int) = 3 * (a : Int) - 2 * (z : Int) := by
            exact Nat.cast_sub hzle
          have hnonneg :
              0 ≤ ((a : Int) - (z : Int)) ^ 2 * ((a : Int) + 2 * (z : Int)) := by
            apply mul_nonneg
            · exact sq_nonneg ((a : Int) - (z : Int))
            · omega
          rw [hcast]
          norm_num
          nlinarith [hnonneg]
        exact_mod_cast hmulInt
      have hmulX : (3 * a - 2 * z) * (z * z) ≤ x := le_trans hmul ha3
      have hdiv : 3 * a - 2 * z ≤ x / (z * z) :=
        (Nat.le_div_iff_mul_le hzz).2 hmulX
      omega
    · have hgt : 3 * a < 2 * z := Nat.lt_of_not_ge hzle
      have hle : a * 3 ≤ z + z := by omega
      exact le_trans hle (Nat.add_le_add_right (Nat.le_add_left z (x / (z * z))) z)
  have hdiv3 : a ≤ (x / (z * z) + z + z) / 3 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2 (by
      simpa [Nat.mul_comm] using hsum)
  exact hdiv3

private theorem cbrtScanStepNat_lower_bound
    (x r shift : Nat)
    (hLower : 1 ≤ x / 2 ^ r) :
    1 ≤ x / 2 ^ cbrtScanStepNat x r shift := by
  unfold cbrtScanStepNat
  by_cases hBranch : 2 ^ shift - 1 < x / 2 ^ r
  · have hBranchLe : 2 ^ shift ≤ x / 2 ^ r := by omega
    have hLower' : 2 ^ 0 ≤ x / 2 ^ (r + shift) :=
      pow2_div_lower_from_div_lower x r 0 shift (by simpa using hBranchLe)
    simpa [hBranch] using hLower'
  · simpa [hBranch] using hLower

private theorem cbrtScanStepNat_upper_bound
    (x r shift : Nat)
    (hUpper : x / 2 ^ r < 2 ^ (shift + shift)) :
    x / 2 ^ cbrtScanStepNat x r shift < 2 ^ shift := by
  unfold cbrtScanStepNat
  by_cases hBranch : 2 ^ shift - 1 < x / 2 ^ r
  · have hUpper' : x / 2 ^ (r + shift) < 2 ^ shift := by
      have h : x / 2 ^ r / 2 ^ shift < 2 ^ shift :=
        pow2_div_upper_from_value_upper (x / 2 ^ r) shift shift hUpper
      simpa [Nat.div_div_eq_div_mul, ← Nat.pow_add] using h
    simpa [hBranch] using hUpper'
  · have hUpper' : x / 2 ^ r < 2 ^ shift := by
      have hPowPos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
      omega
    simpa [hBranch] using hUpper'

private theorem cbrtScanNat_lower_bound (x : Nat) (hx : 2 ^ 8 ≤ x) :
    1 ≤ x / 2 ^ cbrtScanNat x := by
  have h0Lower : 1 ≤ x / 2 ^ 0 := by simpa using (by omega : 1 ≤ x)
  let r1 := cbrtScanStepNat x 0 128
  have h1 : 1 ≤ x / 2 ^ r1 := by
    simpa [r1] using cbrtScanStepNat_lower_bound x 0 128 h0Lower
  let r2 := cbrtScanStepNat x r1 64
  have h2 : 1 ≤ x / 2 ^ r2 := by
    simpa [r2] using cbrtScanStepNat_lower_bound x r1 64 h1
  let r3 := cbrtScanStepNat x r2 32
  have h3 : 1 ≤ x / 2 ^ r3 := by
    simpa [r3] using cbrtScanStepNat_lower_bound x r2 32 h2
  let r4 := cbrtScanStepNat x r3 16
  have h4 : 1 ≤ x / 2 ^ r4 := by
    simpa [r4] using cbrtScanStepNat_lower_bound x r3 16 h3
  let r5 := cbrtScanStepNat x r4 8
  have h5 : 1 ≤ x / 2 ^ r5 := by
    simpa [r5] using cbrtScanStepNat_lower_bound x r4 8 h4
  simpa [cbrtScanNat, r1, r2, r3, r4, r5] using h5

private theorem cbrtScanNat_upper_bound
    (x : Nat) (hxLt : x < 2 ^ 256) :
    x / 2 ^ cbrtScanNat x < 2 ^ 8 := by
  have h0Upper : x / 2 ^ 0 < 2 ^ (128 + 128) := by
    simpa using hxLt
  let r1 := cbrtScanStepNat x 0 128
  have h1 : x / 2 ^ r1 < 2 ^ 128 := by
    simpa [r1] using cbrtScanStepNat_upper_bound x 0 128 h0Upper
  let r2 := cbrtScanStepNat x r1 64
  have h2 : x / 2 ^ r2 < 2 ^ 64 := by
    have hUpper : x / 2 ^ r1 < 2 ^ (64 + 64) := by simpa using h1
    simpa [r2] using cbrtScanStepNat_upper_bound x r1 64 hUpper
  let r3 := cbrtScanStepNat x r2 32
  have h3 : x / 2 ^ r3 < 2 ^ 32 := by
    have hUpper : x / 2 ^ r2 < 2 ^ (32 + 32) := by simpa using h2
    simpa [r3] using cbrtScanStepNat_upper_bound x r2 32 hUpper
  let r4 := cbrtScanStepNat x r3 16
  have h4 : x / 2 ^ r4 < 2 ^ 16 := by
    have hUpper : x / 2 ^ r3 < 2 ^ (16 + 16) := by simpa using h3
    simpa [r4] using cbrtScanStepNat_upper_bound x r3 16 hUpper
  let r5 := cbrtScanStepNat x r4 8
  have h5 : x / 2 ^ r5 < 2 ^ 8 := by
    have hUpper : x / 2 ^ r4 < 2 ^ (8 + 8) := by simpa using h4
    simpa [r5] using cbrtScanStepNat_upper_bound x r4 8 hUpper
  simpa [cbrtScanNat, r1, r2, r3, r4, r5] using h5

private theorem cbrtScanStepNat_mod_8
    (x r shift : Nat) (hr : r % 8 = 0) (hshift : shift % 8 = 0) :
    (cbrtScanStepNat x r shift) % 8 = 0 := by
  unfold cbrtScanStepNat
  by_cases hBranch : 2 ^ shift - 1 < x / 2 ^ r
  · simp [hBranch, Nat.add_mod, hr, hshift]
  · simp [hBranch, hr]

private theorem cbrtScanNat_mod_8 (x : Nat) :
    cbrtScanNat x % 8 = 0 := by
  let r1 := cbrtScanStepNat x 0 128
  have h1 : r1 % 8 = 0 := by
    simpa [r1] using cbrtScanStepNat_mod_8 x 0 128 (by norm_num) (by norm_num)
  let r2 := cbrtScanStepNat x r1 64
  have h2 : r2 % 8 = 0 := by
    simpa [r2] using cbrtScanStepNat_mod_8 x r1 64 h1 (by norm_num)
  let r3 := cbrtScanStepNat x r2 32
  have h3 : r3 % 8 = 0 := by
    simpa [r3] using cbrtScanStepNat_mod_8 x r2 32 h2 (by norm_num)
  let r4 := cbrtScanStepNat x r3 16
  have h4 : r4 % 8 = 0 := by
    simpa [r4] using cbrtScanStepNat_mod_8 x r3 16 h3 (by norm_num)
  let r5 := cbrtScanStepNat x r4 8
  have h5 : r5 % 8 = 0 := by
    simpa [r5] using cbrtScanStepNat_mod_8 x r4 8 h4 (by norm_num)
  simpa [cbrtScanNat, r1, r2, r3, r4, r5] using h5

private theorem cbrtScanStepNat_le_add (x r shift : Nat) :
    cbrtScanStepNat x r shift ≤ r + shift := by
  unfold cbrtScanStepNat
  split <;> omega

private theorem cbrtScanNat_le_248 (x : Nat) :
    cbrtScanNat x ≤ 248 := by
  let r1 := cbrtScanStepNat x 0 128
  have h1 : r1 ≤ 128 := by
    simpa [r1] using cbrtScanStepNat_le_add x 0 128
  let r2 := cbrtScanStepNat x r1 64
  have h2 : r2 ≤ r1 + 64 := by
    simpa [r2] using cbrtScanStepNat_le_add x r1 64
  let r3 := cbrtScanStepNat x r2 32
  have h3 : r3 ≤ r2 + 32 := by
    simpa [r3] using cbrtScanStepNat_le_add x r2 32
  let r4 := cbrtScanStepNat x r3 16
  have h4 : r4 ≤ r3 + 16 := by
    simpa [r4] using cbrtScanStepNat_le_add x r3 16
  let r5 := cbrtScanStepNat x r4 8
  have h5 : r5 ≤ r4 + 8 := by
    simpa [r5] using cbrtScanStepNat_le_add x r4 8
  change r5 ≤ 248
  omega

private noncomputable def realCbrtNat (x : Nat) : ℝ :=
  (x : ℝ) ^ ((3 : ℝ)⁻¹)

private theorem realCbrtNat_nonneg (x : Nat) :
    0 ≤ realCbrtNat x := by
  unfold realCbrtNat
  positivity

private theorem realCbrtNat_pos {x : Nat} (hx : 0 < x) :
    0 < realCbrtNat x := by
  unfold realCbrtNat
  positivity

private theorem realCbrtNat_cube (x : Nat) :
    realCbrtNat x ^ 3 = (x : ℝ) := by
  simpa [realCbrtNat] using
    (Real.rpow_inv_natCast_pow (x := (x : ℝ)) (n := 3)
      (Nat.cast_nonneg x) (by decide : (3 : Nat) ≠ 0))

private theorem natCbrt_le_realCbrtNat (x : Nat) :
    (natCbrt x : ℝ) ≤ realCbrtNat x := by
  by_contra h
  have hGt : realCbrtNat x < (natCbrt x : ℝ) := lt_of_not_ge h
  have hCubeLe : (natCbrt x : ℝ) ^ 3 ≤ realCbrtNat x ^ 3 := by
    rw [realCbrtNat_cube]
    exact_mod_cast natCbrt_cube_le x
  have hCubeGt : realCbrtNat x ^ 3 < (natCbrt x : ℝ) ^ 3 := by
    have haNonneg : (0 : ℝ) ≤ (natCbrt x : ℝ) := by positivity
    exact pow_lt_pow_left₀ hGt (realCbrtNat_nonneg x) (by decide : (3 : Nat) ≠ 0)
  nlinarith

private theorem realCbrtNat_lt_natCbrt_succ (x : Nat) :
    realCbrtNat x < (natCbrt x : ℝ) + 1 := by
  by_contra h
  have hLe : (natCbrt x : ℝ) + 1 ≤ realCbrtNat x := le_of_not_gt h
  have hCubeLe : ((natCbrt x : ℝ) + 1) ^ 3 ≤ realCbrtNat x ^ 3 := by
    have haNonneg : (0 : ℝ) ≤ (natCbrt x : ℝ) + 1 := by positivity
    exact pow_le_pow_left₀ haNonneg hLe 3
  have hCubeGt : realCbrtNat x ^ 3 < ((natCbrt x : ℝ) + 1) ^ 3 := by
    rw [realCbrtNat_cube]
    have h := natCbrt_next_cube_gt x
    exact_mod_cast h
  nlinarith

private theorem cbrtSeed_upper_check :
    ∀ k : Fin 32, ∀ y : Fin 256,
      0 < y.val →
      let r := 8 * k.val
      let seedBase := if 15 < y.val then 30 else 15
      let seed := (seedBase * 2 ^ (r / 3)) / Nat.xor 7 (r % 3)
      125 * seed ^ 3 ≤ 1331 * (2 ^ r * y.val) := by
  native_decide

private theorem cbrtSeed_lower_check :
    ∀ k : Fin 32, ∀ y : Fin 256,
      0 < y.val →
      let r := 8 * k.val
      let seedBase := if 15 < y.val then 30 else 15
      let seed := (seedBase * 2 ^ (r / 3)) / Nat.xor 7 (r % 3)
      343 * (2 ^ r * (y.val + 1)) ≤ 1728 * seed ^ 3 := by
  native_decide

private theorem soladyCbrtSeedNat_real_bounds
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    0 < soladyCbrtSeedNat x ∧
      ((7 : ℝ) / 12) * realCbrtNat x ≤ (soladyCbrtSeedNat x : ℝ) ∧
      (soladyCbrtSeedNat x : ℝ) ≤ ((11 : ℝ) / 5) * realCbrtNat x := by
  let r := cbrtScanNat x
  let y := x / 2 ^ r
  let seedBase := if 15 < y then 30 else 15
  let seed := (seedBase * 2 ^ (r / 3)) / Nat.xor 7 (r % 3)
  have hSeedEq : soladyCbrtSeedNat x = seed := by
    simp [soladyCbrtSeedNat, r, y, seedBase, seed]
  have hyPos : 0 < y := by
    have h : 1 ≤ y := by
      simpa [y, r] using cbrtScanNat_lower_bound x hx
    omega
  have hyUpper : y < 256 := by
    simpa [y, r] using cbrtScanNat_upper_bound x hxLt
  have hPowPos : 0 < 2 ^ r := Nat.pow_pos (by decide : 0 < 2)
  have hXYLe : 2 ^ r * y ≤ x := by
    simpa [y, Nat.mul_comm] using Nat.div_mul_le_self x (2 ^ r)
  have hXUpper : x < 2 ^ r * (y + 1) := by
    simpa [y, Nat.mul_comm] using Nat.lt_mul_div_succ x hPowPos
  have hrMod : r % 8 = 0 := by
    simpa [r] using cbrtScanNat_mod_8 x
  have hrLe : r ≤ 248 := by
    simpa [r] using cbrtScanNat_le_248 x
  have hDvd : 8 ∣ r := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hrMod
  rcases hDvd with ⟨k, hk⟩
  have hkLt : k < 32 := by omega
  let kFin : Fin 32 := ⟨k, hkLt⟩
  let yFin : Fin 256 := ⟨y, hyUpper⟩
  have hUpperCheck := cbrtSeed_upper_check kFin yFin hyPos
  have hLowerCheck := cbrtSeed_lower_check kFin yFin hyPos
  have hUpperCheck' : 125 * seed ^ 3 ≤ 1331 * (2 ^ r * y) := by
    simpa [kFin, yFin, seed, seedBase, hk, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hUpperCheck
  have hLowerCheck' : 343 * (2 ^ r * (y + 1)) ≤ 1728 * seed ^ 3 := by
    simpa [kFin, yFin, seed, seedBase, hk, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hLowerCheck
  have hUpperNat : 125 * seed ^ 3 ≤ 1331 * x := by
    exact le_trans hUpperCheck' (Nat.mul_le_mul_left 1331 hXYLe)
  have hLowerNat : 343 * x < 1728 * seed ^ 3 := by
    exact lt_of_lt_of_le ((mul_lt_mul_left (by decide : 0 < 343)).2 hXUpper)
      hLowerCheck'
  let α := realCbrtNat x
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hαPos : 0 < α := by
    simpa [α] using realCbrtNat_pos hxPos
  have hαCube : α ^ 3 = (x : ℝ) := by
    simpa [α] using realCbrtNat_cube x
  have hSeedUpperR : (seed : ℝ) ≤ ((11 : ℝ) / 5) * α := by
    have hUpperR : (125 : ℝ) * (seed : ℝ) ^ 3 ≤ 1331 * (x : ℝ) := by
      exact_mod_cast hUpperNat
    by_contra hNot
    have hGt : ((11 : ℝ) / 5) * α < (seed : ℝ) := lt_of_not_ge hNot
    have hLeftNonneg : 0 ≤ ((11 : ℝ) / 5) * α := by positivity
    have hPow : (((11 : ℝ) / 5) * α) ^ 3 < (seed : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hGt hLeftNonneg (by decide : (3 : Nat) ≠ 0)
    have hCubeGt : 1331 * (x : ℝ) < 125 * (seed : ℝ) ^ 3 := by
      nlinarith [hPow, hαCube]
    nlinarith
  have hSeedLowerR : ((7 : ℝ) / 12) * α ≤ (seed : ℝ) := by
    have hLowerR : (343 : ℝ) * (x : ℝ) < 1728 * (seed : ℝ) ^ 3 := by
      exact_mod_cast hLowerNat
    by_contra hNot
    have hGt : (seed : ℝ) < ((7 : ℝ) / 12) * α := lt_of_not_ge hNot
    have hSeedNonneg : 0 ≤ (seed : ℝ) := by positivity
    have hPow : (seed : ℝ) ^ 3 < (((7 : ℝ) / 12) * α) ^ 3 :=
      pow_lt_pow_left₀ hGt hSeedNonneg (by decide : (3 : Nat) ≠ 0)
    have hCubeGt : 1728 * (seed : ℝ) ^ 3 < 343 * (x : ℝ) := by
      nlinarith [hPow, hαCube]
    nlinarith
  have hSeedPos : 0 < seed := by
    have hSeedPosR : 0 < (seed : ℝ) := by
      nlinarith
    exact Nat.cast_pos.mp hSeedPosR
  constructor
  · simpa [hSeedEq] using hSeedPos
  · constructor
    · simpa [hSeedEq, α] using hSeedLowerR
    · simpa [hSeedEq, α] using hSeedUpperR

private theorem cbrtSeedNewtonRatioBound
    {t : ℝ} (htPos : 0 < t)
    (hLower : (7 : ℝ) / 12 ≤ t)
    (hUpper : t ≤ (11 : ℝ) / 5) :
    (1 / (t * t) + t + t) / 3 ≤ (929 : ℝ) / 605 := by
  have htNonneg : 0 ≤ t := le_of_lt htPos
  by_cases htOne : t ≤ 1
  · have hA : 0 ≤ 12 * t - 7 := by nlinarith
    have hTSqLe : t ^ 2 ≤ t := by nlinarith
    have hB : 0 ≤ -147 * t ^ 2 + 216 * t + 126 := by nlinarith
    have hPoly : 0 ≤ 3621 * t ^ 2 - 882 - 1764 * t ^ 3 := by
      have hProd : 0 ≤ (12 * t - 7) * (-147 * t ^ 2 + 216 * t + 126) :=
        mul_nonneg hA hB
      have hEq :
          (12 * t - 7) * (-147 * t ^ 2 + 216 * t + 126) =
            3621 * t ^ 2 - 882 - 1764 * t ^ 3 := by
        ring
      rwa [hEq] at hProd
    have hTarget : 882 + 1764 * t ^ 3 ≤ 3621 * t ^ 2 := by nlinarith
    have hLow :
        (1 / (t * t) + t + t) / 3 ≤ (1207 : ℝ) / 882 := by
      calc
        (1 / (t * t) + t + t) / 3
            = (882 + 1764 * t ^ 3) / (2646 * t ^ 2) := by
              field_simp [ne_of_gt htPos]
              ring
        _ ≤ (3621 * t ^ 2) / (2646 * t ^ 2) := by
              exact div_le_div_of_nonneg_right hTarget (by positivity)
        _ = (1207 : ℝ) / 882 := by
              field_simp [ne_of_gt htPos]
              ring
    exact le_trans hLow (by norm_num)
  · have htLowerOne : 1 ≤ t := le_of_not_ge htOne
    have hA : 0 ≤ 11 - 5 * t := by nlinarith
    have hTSqGe : t ≤ t ^ 2 := by nlinarith
    have hB : 0 ≤ 242 * t ^ 2 - 25 * t - 55 := by nlinarith
    have hPoly : 0 ≤ 2787 * t ^ 2 - 605 - 1210 * t ^ 3 := by
      have hProd : 0 ≤ (11 - 5 * t) * (242 * t ^ 2 - 25 * t - 55) :=
        mul_nonneg hA hB
      have hEq :
          (11 - 5 * t) * (242 * t ^ 2 - 25 * t - 55) =
            2787 * t ^ 2 - 605 - 1210 * t ^ 3 := by
        ring
      rwa [hEq] at hProd
    have hTarget : 605 + 1210 * t ^ 3 ≤ 2787 * t ^ 2 := by nlinarith
    calc
      (1 / (t * t) + t + t) / 3
          = (605 + 1210 * t ^ 3) / (1815 * t ^ 2) := by
            field_simp [ne_of_gt htPos]
            ring
      _ ≤ (2787 * t ^ 2) / (1815 * t ^ 2) := by
            exact div_le_div_of_nonneg_right hTarget (by positivity)
      _ = (929 : ℝ) / 605 := by
            field_simp [ne_of_gt htPos]
            ring

private theorem cbrtNewtonRatioUpperAbove
    {u t : ℝ} (hu : 1 ≤ u) (htLower : 1 ≤ t) (htUpper : t ≤ u) :
    (1 / (t * t) + t + t) / 3 ≤ (1 / (u * u) + u + u) / 3 := by
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one htLower
  have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hNonneg : 0 ≤
      (u - t) * (2 * u ^ 2 * t ^ 2 - (u + t)) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr htUpper
    · have htSq : 1 ≤ t ^ 2 := by nlinarith [htLower]
      have hUSqFactor : 1 ≤ u * t ^ 2 :=
        by simpa using mul_le_mul hu htSq zero_le_one (le_of_lt huPos)
      have hU : u ≤ u ^ 2 * t ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hUSqFactor (le_of_lt huPos)
        nlinarith
      have hT : t ≤ u ^ 2 * t ^ 2 := le_trans htUpper hU
      nlinarith
  have hmain :
      0 ≤ (1 / (u * u) + u + u) - (1 / (t * t) + t + t) := by
    have hEq :
        (1 / (u * u) + u + u) - (1 / (t * t) + t + t) =
          ((u - t) * (2 * u ^ 2 * t ^ 2 - (u + t))) / (u ^ 2 * t ^ 2) := by
      field_simp [ne_of_gt huPos, ne_of_gt htPos]
      ring
    rw [hEq]
    exact div_nonneg hNonneg (by positivity)
  linarith

private theorem cbrtStepNat_real_ratio_upper_seed
    (x z : Nat) (hx : 0 < x) (hz : 0 < z)
    (hLowerRatio : (7 : ℝ) / 12 ≤ (z : ℝ) / realCbrtNat x)
    (hUpperRatio : (z : ℝ) / realCbrtNat x ≤ (11 : ℝ) / 5) :
    (cbrtStepNat x z : ℝ) ≤ ((929 : ℝ) / 605) * realCbrtNat x := by
  let α := realCbrtNat x
  have hαPos : 0 < α := by simpa [α] using realCbrtNat_pos hx
  have hαNe : α ≠ 0 := ne_of_gt hαPos
  have hzRealPos : 0 < (z : ℝ) := Nat.cast_pos.2 hz
  have hzRealNe : (z : ℝ) ≠ 0 := ne_of_gt hzRealPos
  have hStepCast :
      (cbrtStepNat x z : ℝ) ≤
        ((x / (z * z) + z + z : Nat) : ℝ) / 3 := by
    unfold cbrtStepNat
    exact Nat.cast_div_le
  have hDivCast :
      ((x / (z * z) : Nat) : ℝ) ≤ (x : ℝ) / ((z : ℝ) * (z : ℝ)) :=
    by simpa using (Nat.cast_div_le (m := x) (n := z * z) : ((x / (z * z) : Nat) : ℝ) ≤ (x : ℝ) / (z * z : Nat))
  have hAddCast :
      ((x / (z * z) + z + z : Nat) : ℝ) / 3 ≤
        ((x : ℝ) / ((z : ℝ) * (z : ℝ)) + (z : ℝ) + (z : ℝ)) / 3 := by
    norm_num
    nlinarith [hDivCast]
  have hRealStep :
      ((x : ℝ) / ((z : ℝ) * (z : ℝ)) + (z : ℝ) + (z : ℝ)) / 3 =
        ((1 / (((z : ℝ) / α) * ((z : ℝ) / α)) +
            (z : ℝ) / α + (z : ℝ) / α) / 3) * α := by
    have hαCube : α ^ 3 = (x : ℝ) := by simpa [α] using realCbrtNat_cube x
    rw [← hαCube]
    field_simp [hαNe, hzRealNe]
    ring
  have htPos : 0 < (z : ℝ) / α := div_pos hzRealPos hαPos
  have hRatio := cbrtSeedNewtonRatioBound htPos
    (by simpa [α] using hLowerRatio) (by simpa [α] using hUpperRatio)
  have hMul := mul_le_mul_of_nonneg_right hRatio (le_of_lt hαPos)
  calc
    (cbrtStepNat x z : ℝ) ≤
        ((x / (z * z) + z + z : Nat) : ℝ) / 3 := hStepCast
    _ ≤ ((x : ℝ) / ((z : ℝ) * (z : ℝ)) + (z : ℝ) + (z : ℝ)) / 3 := hAddCast
    _ = ((1 / (((z : ℝ) / α) * ((z : ℝ) / α)) +
            (z : ℝ) / α + (z : ℝ) / α) / 3) * α := hRealStep
    _ ≤ ((929 : ℝ) / 605) * α := hMul
    _ = ((929 : ℝ) / 605) * realCbrtNat x := rfl

private theorem cbrtStepNat_real_ratio_upper_above
    (x z : Nat) (hx : 0 < x) (hz : 0 < z) {u : ℝ}
    (hu : 1 ≤ u)
    (hLowerRatio : 1 ≤ (z : ℝ) / realCbrtNat x)
    (hUpperRatio : (z : ℝ) / realCbrtNat x ≤ u) :
    (cbrtStepNat x z : ℝ) ≤ ((1 / (u * u) + u + u) / 3) * realCbrtNat x := by
  let α := realCbrtNat x
  have hαPos : 0 < α := by simpa [α] using realCbrtNat_pos hx
  have hαNe : α ≠ 0 := ne_of_gt hαPos
  have hzRealPos : 0 < (z : ℝ) := Nat.cast_pos.2 hz
  have hzRealNe : (z : ℝ) ≠ 0 := ne_of_gt hzRealPos
  have hStepCast :
      (cbrtStepNat x z : ℝ) ≤
        ((x / (z * z) + z + z : Nat) : ℝ) / 3 := by
    unfold cbrtStepNat
    exact Nat.cast_div_le
  have hDivCast :
      ((x / (z * z) : Nat) : ℝ) ≤ (x : ℝ) / ((z : ℝ) * (z : ℝ)) :=
    by simpa using (Nat.cast_div_le (m := x) (n := z * z) : ((x / (z * z) : Nat) : ℝ) ≤ (x : ℝ) / (z * z : Nat))
  have hAddCast :
      ((x / (z * z) + z + z : Nat) : ℝ) / 3 ≤
        ((x : ℝ) / ((z : ℝ) * (z : ℝ)) + (z : ℝ) + (z : ℝ)) / 3 := by
    norm_num
    nlinarith [hDivCast]
  have hRealStep :
      ((x : ℝ) / ((z : ℝ) * (z : ℝ)) + (z : ℝ) + (z : ℝ)) / 3 =
        ((1 / (((z : ℝ) / α) * ((z : ℝ) / α)) +
            (z : ℝ) / α + (z : ℝ) / α) / 3) * α := by
    have hαCube : α ^ 3 = (x : ℝ) := by simpa [α] using realCbrtNat_cube x
    rw [← hαCube]
    field_simp [hαNe, hzRealNe]
    ring
  have hRatio := cbrtNewtonRatioUpperAbove hu
    (by simpa [α] using hLowerRatio) (by simpa [α] using hUpperRatio)
  have hMul := mul_le_mul_of_nonneg_right hRatio (le_of_lt hαPos)
  calc
    (cbrtStepNat x z : ℝ) ≤
        ((x / (z * z) + z + z : Nat) : ℝ) / 3 := hStepCast
    _ ≤ ((x : ℝ) / ((z : ℝ) * (z : ℝ)) + (z : ℝ) + (z : ℝ)) / 3 := hAddCast
    _ = ((1 / (((z : ℝ) / α) * ((z : ℝ) / α)) +
            (z : ℝ) / α + (z : ℝ) / α) / 3) * α := hRealStep
    _ ≤ ((1 / (u * u) + u + u) / 3) * α := hMul
    _ = ((1 / (u * u) + u + u) / 3) * realCbrtNat x := rfl

private def cbrtNewtonTailBoundRat : Nat → ℚ
  | 0 => (929 : ℚ) / 605
  | steps + 1 =>
      let u := cbrtNewtonTailBoundRat steps
      (1 / (u * u) + u + u) / 3

private theorem cbrtNewtonTailBoundRat_ge_one (steps : Nat) :
    1 ≤ cbrtNewtonTailBoundRat steps := by
  induction steps with
  | zero => native_decide
  | succ steps ih =>
      dsimp [cbrtNewtonTailBoundRat]
      let u := cbrtNewtonTailBoundRat steps
      have hu : 1 ≤ u := ih
      have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hNonneg : 0 ≤ (u - 1) ^ 2 * (2 * u + 1) / (u * u) := by
        exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith))
          (mul_nonneg (le_of_lt huPos) (le_of_lt huPos))
      have hEq :
          1 / (u * u) + u + u - 3 =
            (u - 1) ^ 2 * (2 * u + 1) / (u * u) := by
        field_simp [ne_of_gt huPos]
        ring
      have h : 3 ≤ 1 / (u * u) + u + u := by nlinarith
      nlinarith

private theorem cbrtNewtonTailBoundRat_six_tight :
    cbrtNewtonTailBoundRat 6 < (1 : ℚ) + 1 / ((2 : ℚ) ^ 86) := by
  native_decide

private theorem cbrtNewtonTailBoundRat_six_real_tight :
    ((cbrtNewtonTailBoundRat 6 : ℚ) : ℝ) <
      (1 : ℝ) + 1 / ((2 : ℝ) ^ 86) := by
  have hRhs :
      (((1 : ℚ) + 1 / ((2 : ℚ) ^ 86) : ℚ) : ℝ) =
        (1 : ℝ) + 1 / ((2 : ℝ) ^ 86) := by
    norm_num
  rw [← hRhs]
  exact Rat.cast_lt.2 cbrtNewtonTailBoundRat_six_tight

private theorem natCbrt_ge_six_of_ge_256 {x : Nat} (hx : 2 ^ 8 ≤ x) :
    6 ≤ natCbrt x := by
  unfold natCbrt
  exact Nat.le_findGreatest (P := fun r => r ^ 3 ≤ x) (m := 6) (n := x)
    (by omega) (by norm_num; omega)

private theorem cbrtStepNat_near_of_near
    (x z : Nat) (haGe : 6 ≤ natCbrt x)
    (hLower : natCbrt x ≤ z)
    (hUpper : z ≤ natCbrt x + 1) :
    cbrtStepNat x z ≤ natCbrt x + 1 := by
  let a := natCbrt x
  have haPos : 0 < a := by omega
  have hzCases : z = a ∨ z = a + 1 := by omega
  have hNextCube : x < (a + 1) ^ 3 := by
    simpa [a] using natCbrt_next_cube_gt x
  rcases hzCases with hzEq | hzEq
  · have haaPos : 0 < a * a := Nat.mul_pos haPos haPos
    have hDivA : x / (a * a) ≤ a + 3 := by
      have hCubeBound : (a + 1) ^ 3 ≤ (a + 4) * (a * a) := by
        nlinarith [haGe]
      have hDivLt : x / (a * a) < a + 4 :=
        (Nat.div_lt_iff_lt_mul haaPos).2 (lt_of_lt_of_le hNextCube hCubeBound)
      omega
    unfold cbrtStepNat
    rw [hzEq]
    have hNum : x / (a * a) + a + a ≤ 3 * (a + 1) := by omega
    exact Nat.div_le_of_le_mul hNum
  · have hsPos : 0 < (a + 1) * (a + 1) :=
      Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos a)
    have hDivSucc : x / ((a + 1) * (a + 1)) ≤ a := by
      have hDivLt : x / ((a + 1) * (a + 1)) < a + 1 :=
        (Nat.div_lt_iff_lt_mul hsPos).2 (by
          simpa [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hNextCube)
      omega
    unfold cbrtStepNat
    rw [hzEq]
    have hNum : x / ((a + 1) * (a + 1)) + (a + 1) + (a + 1) ≤
        3 * (a + 1) := by omega
    exact Nat.div_le_of_le_mul hNum

private theorem cbrtIterNat_near_or_bound
    (steps k x z : Nat) (hx : 0 < x) (hz : 0 < z)
    (haGe : 6 ≤ natCbrt x)
    (hFloor : natCbrt x ≤ z)
    (hState :
      z ≤ natCbrt x + 1 ∨
        (z : ℝ) ≤ ((cbrtNewtonTailBoundRat k : ℚ) : ℝ) * realCbrtNat x) :
    natCbrt x ≤ cbrtIterNat steps x z ∧
      (cbrtIterNat steps x z ≤ natCbrt x + 1 ∨
        (cbrtIterNat steps x z : ℝ) ≤
          ((cbrtNewtonTailBoundRat (k + steps) : ℚ) : ℝ) * realCbrtNat x) := by
  induction steps generalizing k z with
  | zero =>
      simpa using And.intro hFloor hState
  | succ steps ih =>
      let z1 := cbrtStepNat x z
      have hz1Floor : natCbrt x ≤ z1 := by
        simpa [z1] using cbrtStepNat_ge_floor x z hz
      have hz1Pos : 0 < z1 := by
        simpa [z1] using cbrtStepNat_pos x z hx hz
      have hz1State :
          z1 ≤ natCbrt x + 1 ∨
            (z1 : ℝ) ≤ ((cbrtNewtonTailBoundRat (k + 1) : ℚ) : ℝ) *
              realCbrtNat x := by
        rcases hState with hNear | hBound
        · left
          simpa [z1] using cbrtStepNat_near_of_near x z haGe hFloor hNear
        · by_cases hNear : z ≤ natCbrt x + 1
          · left
            simpa [z1] using cbrtStepNat_near_of_near x z haGe hFloor hNear
          · right
            let u : ℝ := ((cbrtNewtonTailBoundRat k : ℚ) : ℝ)
            have hu : 1 ≤ u := by
              simpa [u] using Rat.cast_le.2 (cbrtNewtonTailBoundRat_ge_one k)
            have hAlphaPos : 0 < realCbrtNat x := realCbrtNat_pos hx
            have hUpperRatio : (z : ℝ) / realCbrtNat x ≤ u := by
              rw [div_le_iff₀ hAlphaPos]
              simpa [u] using hBound
            have hAlphaLtZ : realCbrtNat x < (z : ℝ) := by
              have hAlphaSucc := realCbrtNat_lt_natCbrt_succ x
              have hzGt : natCbrt x + 1 < z := Nat.lt_of_not_ge hNear
              exact lt_trans hAlphaSucc (by exact_mod_cast hzGt)
            have hLowerRatio : (1 : ℝ) ≤ (z : ℝ) / realCbrtNat x := by
              rw [le_div_iff₀ hAlphaPos]
              simpa [one_mul] using le_of_lt hAlphaLtZ
            have hStepUpper := cbrtStepNat_real_ratio_upper_above
              (x := x) (z := z) hx hz (u := u) hu hLowerRatio hUpperRatio
            have hNext :
                (z1 : ℝ) ≤ ((1 / (u * u) + u + u) / 3) * realCbrtNat x := by
              simpa [z1] using hStepUpper
            simpa [z1, u, cbrtNewtonTailBoundRat] using hNext
      have hTail := ih (k + 1) z1 hz1Pos hz1Floor hz1State
      have hIndex : k + 1 + steps = k + (steps + 1) := by omega
      simpa [cbrtIterNat, z1, hIndex] using hTail

private theorem cbrt_near_of_final_ratio_bound
    (x z : Nat) (hx : 0 < x) (hxLt : x < 2 ^ 256)
    (hBound :
      (z : ℝ) ≤ ((cbrtNewtonTailBoundRat 6 : ℚ) : ℝ) * realCbrtNat x) :
    z ≤ natCbrt x + 1 := by
  let α := realCbrtNat x
  have hαPos : 0 < α := by simpa [α] using realCbrtNat_pos hx
  have hαCube : α ^ 3 = (x : ℝ) := by simpa [α] using realCbrtNat_cube x
  have hαLtPow : α < (2 : ℝ) ^ 86 := by
    by_contra hNot
    have hGe : (2 : ℝ) ^ 86 ≤ α := le_of_not_gt hNot
    have hCubeGe : ((2 : ℝ) ^ 86) ^ 3 ≤ α ^ 3 :=
      pow_le_pow_left₀ (by positivity) hGe 3
    have hxLtR : (x : ℝ) < (2 : ℝ) ^ 256 := by exact_mod_cast hxLt
    have hPowGt : (2 : ℝ) ^ 256 < ((2 : ℝ) ^ 86) ^ 3 := by norm_num [pow_mul]
    nlinarith
  have hTight := cbrtNewtonTailBoundRat_six_real_tight
  have hMulTight :
      ((cbrtNewtonTailBoundRat 6 : ℚ) : ℝ) * α <
        ((1 : ℝ) + 1 / ((2 : ℝ) ^ 86)) * α := by
    exact mul_lt_mul_of_pos_right hTight hαPos
  have hExtra : (1 / ((2 : ℝ) ^ 86)) * α < 1 := by
    rw [one_div_mul_eq_div]
    rw [div_lt_one (by positivity : 0 < (2 : ℝ) ^ 86)]
    exact hαLtPow
  have hZLt : (z : ℝ) < α + 1 := by
    nlinarith [hBound, hMulTight, hExtra]
  have hAlphaSucc := realCbrtNat_lt_natCbrt_succ x
  have hZLtNat : (z : ℝ) < (natCbrt x + 2 : Nat) := by
    have h : α + 1 < (natCbrt x : ℝ) + 2 := by nlinarith
    simpa using lt_trans hZLt h
  have hNat : z < natCbrt x + 2 := by exact_mod_cast hZLtNat
  omega

private theorem soladyCbrtBeforeCorrectionNat_near_floor
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    natCbrt x ≤ soladyCbrtBeforeCorrectionNat x ∧
      soladyCbrtBeforeCorrectionNat x ≤ natCbrt x + 1 := by
  let z0 := soladyCbrtSeedNat x
  let z1 := cbrtStepNat x z0
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have haGe : 6 ≤ natCbrt x := natCbrt_ge_six_of_ge_256 hx
  have hSeed := soladyCbrtSeedNat_real_bounds x hx hxLt
  have hz0Pos : 0 < z0 := by simpa [z0] using hSeed.1
  have hαPos : 0 < realCbrtNat x := realCbrtNat_pos hxPos
  have hSeedLowerRatio : (7 : ℝ) / 12 ≤ (z0 : ℝ) / realCbrtNat x := by
    rw [le_div_iff₀ hαPos]
    simpa [z0] using hSeed.2.1
  have hSeedUpperRatio : (z0 : ℝ) / realCbrtNat x ≤ (11 : ℝ) / 5 := by
    rw [div_le_iff₀ hαPos]
    simpa [z0] using hSeed.2.2
  have hStepUpperRaw := cbrtStepNat_real_ratio_upper_seed
    (x := x) (z := z0) hxPos hz0Pos hSeedLowerRatio hSeedUpperRatio
  have hz1Bound :
      (z1 : ℝ) ≤ ((cbrtNewtonTailBoundRat 0 : ℚ) : ℝ) * realCbrtNat x := by
    simpa [z1, cbrtNewtonTailBoundRat] using hStepUpperRaw
  have hz1Floor : natCbrt x ≤ z1 := by
    simpa [z1] using cbrtStepNat_ge_floor x z0 hz0Pos
  have hz1Pos : 0 < z1 := by
    simpa [z1] using cbrtStepNat_pos x z0 hxPos hz0Pos
  have hIter := cbrtIterNat_near_or_bound 6 0 x z1 hxPos hz1Pos haGe
    hz1Floor (Or.inr hz1Bound)
  have hBeforeEq :
      soladyCbrtBeforeCorrectionNat x = cbrtIterNat 6 x z1 := by
    simp [soladyCbrtBeforeCorrectionNat, z0, z1, cbrtIterNat]
  constructor
  · rw [hBeforeEq]
    exact hIter.1
  · rw [hBeforeEq]
    rcases hIter.2 with hNear | hBound
    · exact hNear
    · simpa using cbrt_near_of_final_ratio_bound x (cbrtIterNat 6 x z1) hxPos hxLt hBound

private theorem soladyCbrtNat_property (x : Nat) (hxLt : x < 2 ^ 256) :
    soladyCbrtNat x * soladyCbrtNat x * soladyCbrtNat x ≤ x ∧
      x < (soladyCbrtNat x + 1) * (soladyCbrtNat x + 1) *
        (soladyCbrtNat x + 1) := by
  by_cases hxSmall : x < 2 ^ 8
  · exact soladyCbrtNat_property_of_lt_256 x (by simpa using hxSmall)
  · have hxLarge : 2 ^ 8 ≤ x := Nat.le_of_not_gt hxSmall
    let z := soladyCbrtBeforeCorrectionNat x
    have hNear : natCbrt x ≤ z ∧ z ≤ natCbrt x + 1 := by
      simpa [z] using soladyCbrtBeforeCorrectionNat_near_floor x hxLarge hxLt
    have hzPos : 0 < z := by
      have haGe : 6 ≤ natCbrt x := natCbrt_ge_six_of_ge_256 hxLarge
      omega
    have hBounds := cbrt_near_floor_property x z hNear.1 hNear.2
    simpa [soladyCbrtNat, z] using
      cbrtCorrectNat_property x z hzPos hBounds.1 hBounds.2

private def cbrtIterUint : Nat → Uint256 → Uint256 → Uint256
  | 0, _x, z => z
  | steps + 1, x, z =>
      cbrtIterUint steps x (div (add (add (div x (mul z z)) z) z) 3)

private def cbrtFinishSeedUint (_x r seedBase : Uint256) : Uint256 :=
  div (shl (div r 3) seedBase) (Contracts.bitXor 7 (mod r 3))

private def cbrtBeforeCorrectionUint (x r seedBase : Uint256) : Uint256 :=
  cbrtIterUint 7 x (cbrtFinishSeedUint x r seedBase)

private def cbrtFinishUint (x r seedBase : Uint256) : Uint256 :=
  let z := cbrtBeforeCorrectionUint x r seedBase
  if div x (mul z z) < z then sub z 1 else z

private def cbrtScanSourceUint (x : Uint256) : Uint256 :=
  let r : Uint256 := 0
  let r := if 340282366920938463463374607431768211455 < x then shl 7 1 else r
  let r := if 18446744073709551615 < shr r x then Contracts.bitOr r (shl 6 1) else r
  let r := if 4294967295 < shr r x then Contracts.bitOr r (shl 5 1) else r
  let r := if 65535 < shr r x then Contracts.bitOr r (shl 4 1) else r
  if 255 < shr r x then Contracts.bitOr r (shl 3 1) else r

private def cbrtSeedBaseUint (x r : Uint256) : Uint256 :=
  if 15 < shr r x then 30 else 15

private def cbrtScan3Uint (x r : Uint256) : Uint256 :=
  let r := if 255 < shr r x then Contracts.bitOr r (shl 3 1) else r
  cbrtFinishUint x r (cbrtSeedBaseUint x r)

private def cbrtScan4Uint (x r : Uint256) : Uint256 :=
  if 65535 < shr r x then
    cbrtScan3Uint x (Contracts.bitOr r (shl 4 1))
  else
    cbrtScan3Uint x r

private def cbrtScan5Uint (x r : Uint256) : Uint256 :=
  if 4294967295 < shr r x then
    cbrtScan4Uint x (Contracts.bitOr r (shl 5 1))
  else
    cbrtScan4Uint x r

private def cbrtScan6Uint (x r : Uint256) : Uint256 :=
  if 18446744073709551615 < shr r x then
    cbrtScan5Uint x (Contracts.bitOr r (shl 6 1))
  else
    cbrtScan5Uint x r

private def cbrtSourceUint (x : Uint256) : Uint256 :=
  let r : Uint256 := 0
  if 340282366920938463463374607431768211455 < x then
    cbrtScan6Uint x (shl 7 1)
  else
    cbrtScan6Uint x r

private theorem cbrtScan3Uint_eq_finishScan (x r : Uint256) :
    cbrtScan3Uint x r =
      let r' := if 255 < shr r x then Contracts.bitOr r (shl 3 1) else r
      cbrtFinishUint x r' (cbrtSeedBaseUint x r') := by
  unfold cbrtScan3Uint
  by_cases h : 255 < shr r x
  · simp only [h, if_true]
  · simp only [h, if_false]

private theorem cbrtScan4Uint_eq_finishScan (x r : Uint256) :
    cbrtScan4Uint x r =
      let r1 := if 65535 < shr r x then Contracts.bitOr r (shl 4 1) else r
      let r2 := if 255 < shr r1 x then Contracts.bitOr r1 (shl 3 1) else r1
      cbrtFinishUint x r2 (cbrtSeedBaseUint x r2) := by
  unfold cbrtScan4Uint
  by_cases h : 65535 < shr r x
  · simp only [h, if_true]
    exact cbrtScan3Uint_eq_finishScan x (Contracts.bitOr r (shl 4 1))
  · simp only [h, if_false]
    exact cbrtScan3Uint_eq_finishScan x r

private theorem cbrtScan5Uint_eq_finishScan (x r : Uint256) :
    cbrtScan5Uint x r =
      let r1 := if 4294967295 < shr r x then Contracts.bitOr r (shl 5 1) else r
      let r2 := if 65535 < shr r1 x then Contracts.bitOr r1 (shl 4 1) else r1
      let r3 := if 255 < shr r2 x then Contracts.bitOr r2 (shl 3 1) else r2
      cbrtFinishUint x r3 (cbrtSeedBaseUint x r3) := by
  unfold cbrtScan5Uint
  by_cases h : 4294967295 < shr r x
  · simp only [h, if_true]
    exact cbrtScan4Uint_eq_finishScan x (Contracts.bitOr r (shl 5 1))
  · simp only [h, if_false]
    exact cbrtScan4Uint_eq_finishScan x r

private theorem cbrtScan6Uint_eq_finishScan (x r : Uint256) :
    cbrtScan6Uint x r =
      let r1 := if 18446744073709551615 < shr r x then
        Contracts.bitOr r (shl 6 1) else r
      let r2 := if 4294967295 < shr r1 x then Contracts.bitOr r1 (shl 5 1) else r1
      let r3 := if 65535 < shr r2 x then Contracts.bitOr r2 (shl 4 1) else r2
      let r4 := if 255 < shr r3 x then Contracts.bitOr r3 (shl 3 1) else r3
      cbrtFinishUint x r4 (cbrtSeedBaseUint x r4) := by
  unfold cbrtScan6Uint
  by_cases h : 18446744073709551615 < shr r x
  · simp only [h, if_true]
    exact cbrtScan5Uint_eq_finishScan x (Contracts.bitOr r (shl 6 1))
  · simp only [h, if_false]
    exact cbrtScan5Uint_eq_finishScan x r

private theorem cbrtSourceUint_eq_finishScan (x : Uint256) :
    cbrtSourceUint x =
      cbrtFinishUint x (cbrtScanSourceUint x)
        (cbrtSeedBaseUint x (cbrtScanSourceUint x)) := by
  unfold cbrtSourceUint cbrtScanSourceUint
  by_cases h : 340282366920938463463374607431768211455 < x
  · simp only [h, if_true]
    exact cbrtScan6Uint_eq_finishScan x (shl 7 1)
  · simp only [h, if_false]
    exact cbrtScan6Uint_eq_finishScan x 0

private def cbrtFinishContract (x r seedBase : Uint256) : Contract Uint256 :=
  let z := cbrtBeforeCorrectionUint x r seedBase
  if div x (mul z z) < z then Verity.pure (sub z 1) else Verity.pure z

private def cbrtSeedBaseContract (x r : Uint256) : Contract Uint256 :=
  if 15 < shr r x then
    let seedBase : Uint256 := 30
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtFinishContract x r seedBase
  else
    let seedBase : Uint256 := 15
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtFinishContract x r seedBase

private def cbrtScan3Contract (x r : Uint256) : Contract Uint256 :=
  if 255 < shr r x then
    let r := Contracts.bitOr r (shl 3 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtSeedBaseContract x r
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtSeedBaseContract x r

private def cbrtScan4Contract (x r : Uint256) : Contract Uint256 :=
  if 65535 < shr r x then
    let r := Contracts.bitOr r (shl 4 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan3Contract x r
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan3Contract x r

private def cbrtScan5Contract (x r : Uint256) : Contract Uint256 :=
  if 4294967295 < shr r x then
    let r := Contracts.bitOr r (shl 5 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan4Contract x r
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan4Contract x r

private def cbrtScan6Contract (x r : Uint256) : Contract Uint256 :=
  if 18446744073709551615 < shr r x then
    let r := Contracts.bitOr r (shl 6 1)
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan5Contract x r
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan5Contract x r

private def cbrtSourceContract (x : Uint256) : Contract Uint256 :=
  let r : Uint256 := 0
  if 340282366920938463463374607431768211455 < x then
    let r := shl 7 1
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan6Contract x r
  else
    Verity.bind (Verity.pure PUnit.unit) fun _ => cbrtScan6Contract x r

private theorem cbrtFinishIf_run_eq_uint (x z : Uint256) (s : ContractState) :
    ((if div x (mul z z) < z then Verity.pure (sub z 1) else Verity.pure z).run s).fst =
      if div x (mul z z) < z then sub z 1 else z := by
  by_cases h : div x (mul z z) < z
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

private theorem cbrtFinishContract_run_eq_uint
    (x r seedBase : Uint256) (s : ContractState) :
    ((cbrtFinishContract x r seedBase).run s).fst = cbrtFinishUint x r seedBase := by
  unfold cbrtFinishContract cbrtFinishUint
  exact cbrtFinishIf_run_eq_uint x (cbrtBeforeCorrectionUint x r seedBase) s

private theorem cbrtSeedBaseContract_run_eq_uint
    (x r : Uint256) (s : ContractState) :
    ((cbrtSeedBaseContract x r).run s).fst =
      cbrtFinishUint x r (cbrtSeedBaseUint x r) := by
  unfold cbrtSeedBaseContract cbrtSeedBaseUint
  by_cases h : 15 < shr r x
  · simp only [h, if_true, bind_pure_contract, cbrtFinishContract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, cbrtFinishContract_run_eq_uint]

private theorem cbrtScan3Contract_run_eq_uint
    (x r : Uint256) (s : ContractState) :
    ((cbrtScan3Contract x r).run s).fst = cbrtScan3Uint x r := by
  unfold cbrtScan3Contract cbrtScan3Uint
  by_cases h : 255 < shr r x
  · simp only [h, if_true, bind_pure_contract, cbrtSeedBaseContract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, cbrtSeedBaseContract_run_eq_uint]

private theorem cbrtScan4Contract_run_eq_uint
    (x r : Uint256) (s : ContractState) :
    ((cbrtScan4Contract x r).run s).fst = cbrtScan4Uint x r := by
  unfold cbrtScan4Contract cbrtScan4Uint
  by_cases h : 65535 < shr r x
  · simp only [h, if_true, bind_pure_contract, cbrtScan3Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, cbrtScan3Contract_run_eq_uint]

private theorem cbrtScan5Contract_run_eq_uint
    (x r : Uint256) (s : ContractState) :
    ((cbrtScan5Contract x r).run s).fst = cbrtScan5Uint x r := by
  unfold cbrtScan5Contract cbrtScan5Uint
  by_cases h : 4294967295 < shr r x
  · simp only [h, if_true, bind_pure_contract, cbrtScan4Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, cbrtScan4Contract_run_eq_uint]

private theorem cbrtScan6Contract_run_eq_uint
    (x r : Uint256) (s : ContractState) :
    ((cbrtScan6Contract x r).run s).fst = cbrtScan6Uint x r := by
  unfold cbrtScan6Contract cbrtScan6Uint
  by_cases h : 18446744073709551615 < shr r x
  · simp only [h, if_true, bind_pure_contract, cbrtScan5Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, cbrtScan5Contract_run_eq_uint]

private theorem cbrtSourceContract_run_eq_uint (x : Uint256) (s : ContractState) :
    ((cbrtSourceContract x).run s).fst = cbrtSourceUint x := by
  unfold cbrtSourceContract cbrtSourceUint
  by_cases h : 340282366920938463463374607431768211455 < x
  · simp only [h, if_true, bind_pure_contract, cbrtScan6Contract_run_eq_uint]
  · simp only [h, if_false, bind_pure_contract, cbrtScan6Contract_run_eq_uint]

private theorem cbrt_run_eq_sourceUint (x : Uint256) (s : ContractState) :
    ((cbrt x).run s).fst = cbrtSourceUint x := by
  rw [cbrt, Tamago.Utils.FixedPointMathLibBase.cbrt.eq_1]
  unfold cbrtSourceUint
  by_cases h : 340282366920938463463374607431768211455 < x
  · simp only [h, if_true, bind_pure_contract]
    change ((cbrtScan6Contract x (shl 7 1)).run s).fst =
      cbrtScan6Uint x (shl 7 1)
    exact cbrtScan6Contract_run_eq_uint x (shl 7 1) s
  · simp only [h, if_false, bind_pure_contract]
    change ((cbrtScan6Contract x 0).run s).fst = cbrtScan6Uint x 0
    exact cbrtScan6Contract_run_eq_uint x 0 s

private theorem cbrtSourceUint_val_small :
    ∀ x : Fin 256,
      (cbrtSourceUint (uintOfNat x.val)).val = soladyCbrtNat x.val := by
  native_decide

@[simp] private theorem cbrtThreshold128_val :
    (340282366920938463463374607431768211455 : Uint256).val = 2 ^ 128 - 1 := by
  native_decide

@[simp] private theorem cbrtThreshold64_val :
    (18446744073709551615 : Uint256).val = 2 ^ 64 - 1 := by
  native_decide

@[simp] private theorem cbrtThreshold32_val :
    (4294967295 : Uint256).val = 2 ^ 32 - 1 := by
  native_decide

@[simp] private theorem cbrtThreshold16_val :
    (65535 : Uint256).val = 2 ^ 16 - 1 := by
  native_decide

@[simp] private theorem cbrtThreshold8_val :
    (255 : Uint256).val = 2 ^ 8 - 1 := by
  native_decide

@[simp] private theorem shl_3_1_val : (shl 3 1).val = 8 := by
  native_decide

private theorem cbrtScanStepUint_val
    (x r shiftWord thresholdWord : Uint256) (rn shift : Nat)
    (hr : r.val = rn)
    (hThreshold : thresholdWord.val = 2 ^ shift - 1)
    (hOr : (Contracts.bitOr r shiftWord).val = rn + shift) :
    (if thresholdWord < shr r x then Contracts.bitOr r shiftWord else r).val =
      cbrtScanStepNat x.val rn shift := by
  unfold cbrtScanStepNat
  have hBranch :
      (thresholdWord < shr r x) ↔
        2 ^ shift - 1 < x.val / 2 ^ rn := by
    change thresholdWord.val < (shr r x).val ↔
      2 ^ shift - 1 < x.val / 2 ^ rn
    rw [shr_val, hr, hThreshold]
  by_cases h : 2 ^ shift - 1 < x.val / 2 ^ rn
  · have hUint := hBranch.mpr h
    rw [if_pos hUint, if_pos h]
    exact hOr
  · have hUint : ¬ thresholdWord < shr r x := fun hh => h (hBranch.mp hh)
    rw [if_neg hUint, if_neg h]
    exact hr

private theorem bitOr_shl_3_1_cbrtScan_val
    (r : Uint256) {rn : Nat} (hr : r.val = rn)
    (hrn :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224 ∨
          rn = 16 ∨ rn = 144 ∨ rn = 80 ∨ rn = 208 ∨
            rn = 48 ∨ rn = 176 ∨ rn = 112 ∨ rn = 240) :
    (Contracts.bitOr r (shl 3 1)).val = rn + 8 := by
  rcases hrn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [bitOr_val, hr, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] <;>
    native_decide

private theorem cbrtScanStepNat_128_possible (x : Nat) :
    cbrtScanStepNat x 0 128 = 0 ∨ cbrtScanStepNat x 0 128 = 128 := by
  unfold cbrtScanStepNat
  split <;> omega

private theorem cbrtScanStepNat_64_possible
    (x rn : Nat) (hrn : rn = 0 ∨ rn = 128) :
    cbrtScanStepNat x rn 64 = 0 ∨ cbrtScanStepNat x rn 64 = 128 ∨
      cbrtScanStepNat x rn 64 = 64 ∨ cbrtScanStepNat x rn 64 = 192 := by
  unfold cbrtScanStepNat
  rcases hrn with rfl | rfl
  all_goals
    split <;> omega

private theorem cbrtScanStepNat_32_possible
    (x rn : Nat)
    (hrn : rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192) :
    cbrtScanStepNat x rn 32 = 0 ∨ cbrtScanStepNat x rn 32 = 128 ∨
      cbrtScanStepNat x rn 32 = 64 ∨ cbrtScanStepNat x rn 32 = 192 ∨
        cbrtScanStepNat x rn 32 = 32 ∨ cbrtScanStepNat x rn 32 = 160 ∨
          cbrtScanStepNat x rn 32 = 96 ∨ cbrtScanStepNat x rn 32 = 224 := by
  unfold cbrtScanStepNat
  rcases hrn with rfl | rfl | rfl | rfl
  all_goals
    split <;> omega

private theorem cbrtScanStepNat_16_possible
    (x rn : Nat)
    (hrn :
      rn = 0 ∨ rn = 128 ∨ rn = 64 ∨ rn = 192 ∨
        rn = 32 ∨ rn = 160 ∨ rn = 96 ∨ rn = 224) :
    cbrtScanStepNat x rn 16 = 0 ∨ cbrtScanStepNat x rn 16 = 128 ∨
      cbrtScanStepNat x rn 16 = 64 ∨ cbrtScanStepNat x rn 16 = 192 ∨
        cbrtScanStepNat x rn 16 = 32 ∨ cbrtScanStepNat x rn 16 = 160 ∨
          cbrtScanStepNat x rn 16 = 96 ∨ cbrtScanStepNat x rn 16 = 224 ∨
            cbrtScanStepNat x rn 16 = 16 ∨ cbrtScanStepNat x rn 16 = 144 ∨
              cbrtScanStepNat x rn 16 = 80 ∨ cbrtScanStepNat x rn 16 = 208 ∨
                cbrtScanStepNat x rn 16 = 48 ∨ cbrtScanStepNat x rn 16 = 176 ∨
                  cbrtScanStepNat x rn 16 = 112 ∨ cbrtScanStepNat x rn 16 = 240 := by
  unfold cbrtScanStepNat
  rcases hrn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    split <;> omega

private theorem cbrtScanSourceUint_val (x : Uint256) :
    (cbrtScanSourceUint x).val = cbrtScanNat x.val := by
  unfold cbrtScanSourceUint cbrtScanNat
  let ru1 : Uint256 :=
    if 340282366920938463463374607431768211455 < x then shl 7 1 else 0
  let rn1 : Nat := cbrtScanStepNat x.val 0 128
  have hru1 : ru1.val = rn1 := by
    dsimp [ru1, rn1, cbrtScanStepNat]
    have hBranch :
        (340282366920938463463374607431768211455 < x) ↔
          2 ^ 128 - 1 < x.val / 2 ^ 0 := by
      change (340282366920938463463374607431768211455 : Uint256).val < x.val ↔
        2 ^ 128 - 1 < x.val / 2 ^ 0
      rw [cbrtThreshold128_val]
      norm_num
    by_cases h : 2 ^ 128 - 1 < x.val / 2 ^ 0
    · have hUint := hBranch.mpr h
      have hUintVal :
          (340282366920938463463374607431768211455 : Uint256).val < x.val := hUint
      have hNat : 340282366920938463463374607431768211455 < x.val / 1 := by
        simpa using h
      rw [if_pos hUintVal, if_pos hNat]
      exact shl_7_1_val
    · have hUint : ¬ 340282366920938463463374607431768211455 < x :=
        fun hh => h (hBranch.mp hh)
      have hUintVal :
          ¬ (340282366920938463463374607431768211455 : Uint256).val < x.val := hUint
      have hNat : ¬ 340282366920938463463374607431768211455 < x.val / 1 := by
        simpa using h
      rw [if_neg hUintVal, if_neg hNat]
      rfl
  let ru2 : Uint256 :=
    if 18446744073709551615 < shr ru1 x then
      Contracts.bitOr ru1 (shl 6 1)
    else
      ru1
  let rn2 : Nat := cbrtScanStepNat x.val rn1 64
  have hrn1 : rn1 = 0 ∨ rn1 = 128 := by
    simpa [rn1] using cbrtScanStepNat_128_possible x.val
  have hOr2 : (Contracts.bitOr ru1 (shl 6 1)).val = rn1 + 64 := by
    exact bitOr_shl_6_1_sqrtScan_val ru1 hru1 hrn1
  have hru2 : ru2.val = rn2 := by
    dsimp [ru2, rn2]
    exact cbrtScanStepUint_val x ru1 (shl 6 1) 18446744073709551615 rn1 64
      hru1 (by norm_num) hOr2
  let ru3 : Uint256 :=
    if 4294967295 < shr ru2 x then
      Contracts.bitOr ru2 (shl 5 1)
    else
      ru2
  let rn3 : Nat := cbrtScanStepNat x.val rn2 32
  have hrn2 : rn2 = 0 ∨ rn2 = 128 ∨ rn2 = 64 ∨ rn2 = 192 := by
    simpa [rn2] using cbrtScanStepNat_64_possible x.val rn1 hrn1
  have hOr3 : (Contracts.bitOr ru2 (shl 5 1)).val = rn2 + 32 := by
    exact bitOr_shl_5_1_sqrtScan_val ru2 hru2 hrn2
  have hru3 : ru3.val = rn3 := by
    dsimp [ru3, rn3]
    exact cbrtScanStepUint_val x ru2 (shl 5 1) 4294967295 rn2 32
      hru2 (by norm_num) hOr3
  let ru4 : Uint256 :=
    if 65535 < shr ru3 x then
      Contracts.bitOr ru3 (shl 4 1)
    else
      ru3
  let rn4 : Nat := cbrtScanStepNat x.val rn3 16
  have hrn3 :
      rn3 = 0 ∨ rn3 = 128 ∨ rn3 = 64 ∨ rn3 = 192 ∨
        rn3 = 32 ∨ rn3 = 160 ∨ rn3 = 96 ∨ rn3 = 224 := by
    simpa [rn3] using cbrtScanStepNat_32_possible x.val rn2 hrn2
  have hOr4 : (Contracts.bitOr ru3 (shl 4 1)).val = rn3 + 16 := by
    exact bitOr_shl_4_1_sqrtScan_val ru3 hru3 hrn3
  have hru4 : ru4.val = rn4 := by
    dsimp [ru4, rn4]
    exact cbrtScanStepUint_val x ru3 (shl 4 1) 65535 rn3 16
      hru3 (by norm_num) hOr4
  let ru5 : Uint256 :=
    if 255 < shr ru4 x then
      Contracts.bitOr ru4 (shl 3 1)
    else
      ru4
  let rn5 : Nat := cbrtScanStepNat x.val rn4 8
  have hrn4 :
      rn4 = 0 ∨ rn4 = 128 ∨ rn4 = 64 ∨ rn4 = 192 ∨
        rn4 = 32 ∨ rn4 = 160 ∨ rn4 = 96 ∨ rn4 = 224 ∨
          rn4 = 16 ∨ rn4 = 144 ∨ rn4 = 80 ∨ rn4 = 208 ∨
            rn4 = 48 ∨ rn4 = 176 ∨ rn4 = 112 ∨ rn4 = 240 := by
    simpa [rn4] using cbrtScanStepNat_16_possible x.val rn3 hrn3
  have hOr5 : (Contracts.bitOr ru4 (shl 3 1)).val = rn4 + 8 := by
    exact bitOr_shl_3_1_cbrtScan_val ru4 hru4 hrn4
  have hru5 : ru5.val = rn5 := by
    dsimp [ru5, rn5]
    exact cbrtScanStepUint_val x ru4 (shl 3 1) 255 rn4 8
      hru4 (by norm_num) hOr5
  change ru5.val = rn5
  exact hru5

private theorem uint3_val : (3 : Uint256).val = 3 := by
  native_decide

private theorem uint7_val : (7 : Uint256).val = 7 := by
  native_decide

private theorem uint15_val : (15 : Uint256).val = 15 := by
  native_decide

private theorem uint30_val : (30 : Uint256).val = 30 := by
  native_decide

private theorem cbrtSeedBaseUint_val
    (x rU : Uint256) {r : Nat} (hr : rU.val = r) :
    (cbrtSeedBaseUint x rU).val =
      if 15 < x.val / 2 ^ r then 30 else 15 := by
  unfold cbrtSeedBaseUint
  have hBranch :
      (15 < shr rU x) ↔ 15 < x.val / 2 ^ r := by
    change (15 : Uint256).val < (shr rU x).val ↔ 15 < x.val / 2 ^ r
    rw [uint15_val, shr_val, hr]
  by_cases h : 15 < x.val / 2 ^ r
  · have hUint := hBranch.mpr h
    rw [if_pos hUint, if_pos h]
    exact uint30_val
  · have hUint : ¬ 15 < shr rU x := fun hh => h (hBranch.mp hh)
    rw [if_neg hUint, if_neg h]
    exact uint15_val

private theorem cbrtFinishSeedUint_val_large
    (x : Uint256) (_hx : 2 ^ 8 ≤ x.val) :
    (cbrtFinishSeedUint x (cbrtScanSourceUint x)
      (cbrtSeedBaseUint x (cbrtScanSourceUint x))).val =
      soladyCbrtSeedNat x.val := by
  let rU := cbrtScanSourceUint x
  let r := cbrtScanNat x.val
  let seedBaseU := cbrtSeedBaseUint x rU
  let seedBase := if 15 < x.val / 2 ^ r then 30 else 15
  have hR : rU.val = r := by
    simpa [rU, r] using cbrtScanSourceUint_val x
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hrLe : r ≤ 248 := by
    simpa [r] using cbrtScanNat_le_248 x.val
  have hrDivLe : r / 3 ≤ 82 := by omega
  have hSeedBaseVal : seedBaseU.val = seedBase := by
    simpa [seedBaseU, seedBase] using cbrtSeedBaseUint_val x rU hR
  have hSeedBaseLe : seedBase ≤ 30 := by
    by_cases h : 15 < x.val / 2 ^ r <;> simp [seedBase, h]
  have hDivRVal : (div rU 3).val = r / 3 := by
    rw [div_val rU 3 (by rw [uint3_val]; norm_num), hR, uint3_val]
  have hModRVal : (mod rU 3).val = r % 3 := by
    rw [mod_val rU 3 (by rw [uint3_val]; norm_num), hR, uint3_val]
  have hShlLt : seedBaseU.val * 2 ^ (div rU 3).val <
      Verity.Core.Uint256.modulus := by
    rw [hSeedBaseVal, hDivRVal]
    have hPow : 2 ^ (r / 3) ≤ 2 ^ 82 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrDivLe
    have hScaledLe : seedBase * 2 ^ (r / 3) ≤ 30 * 2 ^ 82 :=
      Nat.mul_le_mul hSeedBaseLe hPow
    have hBound : 30 * 2 ^ 82 < Verity.Core.Uint256.modulus := by
      native_decide
    exact lt_of_le_of_lt hScaledLe hBound
  have hScaledVal :
      (shl (div rU 3) seedBaseU).val = seedBase * 2 ^ (r / 3) := by
    rw [shl_small_val _ _ hShlLt, hSeedBaseVal, hDivRVal]
  have hModCases : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by
    have hModLt := Nat.mod_lt r (by decide : 0 < 3)
    omega
  have hXorVal :
      (Contracts.bitXor 7 (mod rU 3)).val = Nat.xor 7 (r % 3) := by
    rw [bitXor_val, uint7_val, hModRVal]
    apply Nat.mod_eq_of_lt
    rcases hModCases with hMod | hMod | hMod <;>
      simp [hMod, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] <;>
      native_decide
  have hXorNe : (Contracts.bitXor 7 (mod rU 3)).val ≠ 0 := by
    rw [hXorVal]
    rcases hModCases with hMod | hMod | hMod <;> simp [hMod]
  have hDivSeedVal :
      (div (shl (div rU 3) seedBaseU) (Contracts.bitXor 7 (mod rU 3))).val =
        (seedBase * 2 ^ (r / 3)) / Nat.xor 7 (r % 3) := by
    rw [div_val _ _ hXorNe, hScaledVal, hXorVal]
  simpa [cbrtFinishSeedUint, soladyCbrtSeedNat, rU, r, seedBaseU, seedBase]
    using hDivSeedVal

private theorem realCbrtNat_lt_pow86 {x : Nat} (hxLt : x < 2 ^ 256) :
    realCbrtNat x < (2 : ℝ) ^ 86 := by
  let α := realCbrtNat x
  have hαCube : α ^ 3 = (x : ℝ) := by simpa [α] using realCbrtNat_cube x
  by_contra hNot
  have hGe : (2 : ℝ) ^ 86 ≤ α := le_of_not_gt hNot
  have hCubeGe : ((2 : ℝ) ^ 86) ^ 3 ≤ α ^ 3 :=
    pow_le_pow_left₀ (by positivity) hGe 3
  have hxLtR : (x : ℝ) < (2 : ℝ) ^ 256 := by exact_mod_cast hxLt
  have hPowGt : (2 : ℝ) ^ 256 < ((2 : ℝ) ^ 86) ^ 3 := by norm_num [pow_mul]
  nlinarith

private theorem natCbrt_lt_pow86 {x : Nat} (hxLt : x < 2 ^ 256) :
    natCbrt x < 2 ^ 86 := by
  by_contra hNot
  have hLe : 2 ^ 86 ≤ natCbrt x := Nat.le_of_not_gt hNot
  have hCubeLe : (2 ^ 86 : Nat) ^ 3 ≤ natCbrt x ^ 3 :=
    Nat.pow_le_pow_left hLe 3
  have hFloor := natCbrt_cube_le x
  have hPowGt : 2 ^ 256 < (2 ^ 86 : Nat) ^ 3 := by
    native_decide
  omega

private theorem cbrt_square_no_overflow_of_le_three_pow86 {z : Nat}
    (hUpper : z ≤ 3 * 2 ^ 86) :
    z * z < Verity.Core.Uint256.modulus := by
  have hSq : z * z ≤ (3 * 2 ^ 86) * (3 * 2 ^ 86) :=
    Nat.mul_le_mul hUpper hUpper
  have hBound :
      (3 * 2 ^ 86) * (3 * 2 ^ 86) < Verity.Core.Uint256.modulus := by
    native_decide
  exact lt_of_le_of_lt hSq hBound

private theorem div_le_cbrt_add_six
    (x z : Nat) (haPos : 0 < natCbrt x) (hFloor : natCbrt x ≤ z) :
    x / (z * z) ≤ natCbrt x + 6 := by
  let a := natCbrt x
  have haaPos : 0 < a * a := Nat.mul_pos (by simpa [a] using haPos)
    (by simpa [a] using haPos)
  have hzz : a * a ≤ z * z := Nat.mul_le_mul hFloor hFloor
  have hDivMono : x / (z * z) ≤ x / (a * a) :=
    Nat.div_le_div_left hzz (by simpa [a] using haaPos)
  have hNextCube : x < (a + 1) ^ 3 := by
    simpa [a] using natCbrt_next_cube_gt x
  have hCubeBound : (a + 1) ^ 3 ≤ (a + 7) * (a * a) := by
    nlinarith [haPos]
  have hDivLt : x / (a * a) < a + 7 :=
    (Nat.div_lt_iff_lt_mul (by simpa [a] using haaPos)).2
      (lt_of_lt_of_le hNextCube hCubeBound)
  omega

private theorem cbrtStepNat_add_no_overflow
    (x z : Nat) (hxLt : x < 2 ^ 256) (haPos : 0 < natCbrt x)
    (hFloor : natCbrt x ≤ z) (hUpper : z ≤ 3 * 2 ^ 86) :
    x / (z * z) + z + z < Verity.Core.Uint256.modulus := by
  have hDivLe := div_le_cbrt_add_six x z haPos hFloor
  have hCbrtLt := natCbrt_lt_pow86 (x := x) hxLt
  have hNumLe : x / (z * z) + z + z ≤ 7 * 2 ^ 86 + 6 := by omega
  have hBound : 7 * 2 ^ 86 + 6 < Verity.Core.Uint256.modulus := by
    native_decide
  exact lt_of_le_of_lt hNumLe hBound

private theorem cbrtStepNat_le_three_pow86
    (x z : Nat) (hxLt : x < 2 ^ 256) (haPos : 0 < natCbrt x)
    (hFloor : natCbrt x ≤ z) (hUpper : z ≤ 3 * 2 ^ 86) :
    cbrtStepNat x z ≤ 3 * 2 ^ 86 := by
  unfold cbrtStepNat
  have hDivLe := div_le_cbrt_add_six x z haPos hFloor
  have hCbrtLt := natCbrt_lt_pow86 (x := x) hxLt
  have hNumLe : x / (z * z) + z + z ≤ 7 * 2 ^ 86 + 6 := by omega
  have hDiv : (x / (z * z) + z + z) / 3 ≤ (7 * 2 ^ 86 + 6) / 3 :=
    Nat.div_le_div_right hNumLe
  have hBound : (7 * 2 ^ 86 + 6) / 3 ≤ 3 * 2 ^ 86 := by
    native_decide
  exact le_trans hDiv hBound

private theorem cbrtSeedNat_le_three_pow86
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    soladyCbrtSeedNat x ≤ 3 * 2 ^ 86 := by
  let z := soladyCbrtSeedNat x
  let α := realCbrtNat x
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hSeed := soladyCbrtSeedNat_real_bounds x hx hxLt
  have hαLt : α < (2 : ℝ) ^ 86 := by simpa [α] using realCbrtNat_lt_pow86 hxLt
  have hzUpperR : (z : ℝ) < 3 * (2 : ℝ) ^ 86 := by
    have h : (z : ℝ) ≤ ((11 : ℝ) / 5) * α := by
      simpa [z, α] using hSeed.2.2
    nlinarith
  exact le_of_lt (by exact_mod_cast hzUpperR)

private theorem cbrtSeedNat_add_no_overflow
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    x / (soladyCbrtSeedNat x * soladyCbrtSeedNat x) +
        soladyCbrtSeedNat x + soladyCbrtSeedNat x <
      Verity.Core.Uint256.modulus := by
  let z := soladyCbrtSeedNat x
  let α := realCbrtNat x
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hSeed := soladyCbrtSeedNat_real_bounds x hx hxLt
  have hzPos : 0 < z := by simpa [z] using hSeed.1
  have hαPos : 0 < α := by simpa [α] using realCbrtNat_pos hxPos
  have hαCube : α ^ 3 = (x : ℝ) := by simpa [α] using realCbrtNat_cube x
  have hαLt : α < (2 : ℝ) ^ 86 := by simpa [α] using realCbrtNat_lt_pow86 hxLt
  have hzUpper : z < 3 * 2 ^ 86 := by
    have hzUpperR : (z : ℝ) < 3 * (2 : ℝ) ^ 86 := by
      have h : (z : ℝ) ≤ ((11 : ℝ) / 5) * α := by
        simpa [z, α] using hSeed.2.2
      nlinarith
    exact_mod_cast hzUpperR
  have hDivUpperR :
      ((x / (z * z) : Nat) : ℝ) < 3 * (2 : ℝ) ^ 86 := by
    have hDivCast :
        ((x / (z * z) : Nat) : ℝ) ≤ (x : ℝ) / ((z : ℝ) * (z : ℝ)) :=
      by simpa using
        (Nat.cast_div_le (m := x) (n := z * z) :
          ((x / (z * z) : Nat) : ℝ) ≤ (x : ℝ) / (z * z : Nat))
    have hzLower : ((7 : ℝ) / 12) * α ≤ (z : ℝ) := by
      simpa [z, α] using hSeed.2.1
    have hzPosR : 0 < (z : ℝ) := Nat.cast_pos.2 hzPos
    have hDivReal :
        (x : ℝ) / ((z : ℝ) * (z : ℝ)) ≤ ((144 : ℝ) / 49) * α := by
      rw [← hαCube]
      rw [div_le_iff₀ (mul_pos hzPosR hzPosR)]
      have hLowerSq : (((7 : ℝ) / 12) * α) ^ 2 ≤ (z : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hzLower 2
      nlinarith [hLowerSq, hαPos]
    have hBound : ((144 : ℝ) / 49) * α < 3 * (2 : ℝ) ^ 86 := by
      nlinarith
    exact lt_of_le_of_lt (le_trans hDivCast hDivReal) hBound
  have hDivUpper : x / (z * z) < 3 * 2 ^ 86 := by
    exact_mod_cast hDivUpperR
  have hSum : x / (z * z) + z + z < 9 * 2 ^ 86 := by omega
  have hBound : 9 * 2 ^ 86 < Verity.Core.Uint256.modulus := by
    native_decide
  simpa [z] using lt_trans hSum hBound

private theorem cbrtSeedStepNat_le_three_pow86
    (x : Nat) (hx : 2 ^ 8 ≤ x) (hxLt : x < 2 ^ 256) :
    cbrtStepNat x (soladyCbrtSeedNat x) ≤ 3 * 2 ^ 86 := by
  let z := soladyCbrtSeedNat x
  let α := realCbrtNat x
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 8) hx
  have hSeed := soladyCbrtSeedNat_real_bounds x hx hxLt
  have hzPos : 0 < z := by simpa [z] using hSeed.1
  have hαPos : 0 < α := by simpa [α] using realCbrtNat_pos hxPos
  have hαLt : α < (2 : ℝ) ^ 86 := by simpa [α] using realCbrtNat_lt_pow86 hxLt
  have hSeedLowerRatio : (7 : ℝ) / 12 ≤ (z : ℝ) / α := by
    rw [le_div_iff₀ hαPos]
    simpa [z, α] using hSeed.2.1
  have hSeedUpperRatio : (z : ℝ) / α ≤ (11 : ℝ) / 5 := by
    rw [div_le_iff₀ hαPos]
    simpa [z, α] using hSeed.2.2
  have hStepUpper := cbrtStepNat_real_ratio_upper_seed
    (x := x) (z := z) hxPos hzPos hSeedLowerRatio hSeedUpperRatio
  have hStepR : (cbrtStepNat x z : ℝ) < 3 * (2 : ℝ) ^ 86 := by
    nlinarith
  exact le_of_lt (by exact_mod_cast hStepR)

private theorem cbrtStepUint_val
    (x zU : Uint256) (z : Nat)
    (hzVal : zU.val = z) (hzPos : 0 < z)
    (hMulLt : z * z < Verity.Core.Uint256.modulus)
    (hAddLt : x.val / (z * z) + z + z < Verity.Core.Uint256.modulus) :
    (div (add (add (div x (mul zU zU)) zU) zU) 3).val =
      cbrtStepNat x.val z := by
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
  unfold cbrtStepNat
  rw [div_val _ 3 hThreeNe, hAdd2Val, uint3_val]

private theorem cbrtIterUint_val_of_nat_floor
    (steps : Nat) (x zU : Uint256) (z : Nat)
    (hxLt : x.val < 2 ^ 256) (haPos : 0 < natCbrt x.val)
    (hzVal : zU.val = z)
    (hFloor : natCbrt x.val ≤ z) (hUpper : z ≤ 3 * 2 ^ 86) :
    (cbrtIterUint steps x zU).val = cbrtIterNat steps x.val z := by
  induction steps generalizing zU z with
  | zero =>
      simpa [cbrtIterUint, cbrtIterNat] using hzVal
  | succ steps ih =>
      have hzPos : 0 < z := lt_of_lt_of_le haPos hFloor
      have hMulLt := cbrt_square_no_overflow_of_le_three_pow86 hUpper
      have hAddLt := cbrtStepNat_add_no_overflow x.val z hxLt haPos hFloor hUpper
      have hStepVal :
          (div (add (add (div x (mul zU zU)) zU) zU) 3).val =
            cbrtStepNat x.val z :=
        cbrtStepUint_val x zU z hzVal hzPos hMulLt hAddLt
      have hNextFloor : natCbrt x.val ≤ cbrtStepNat x.val z :=
        cbrtStepNat_ge_floor x.val z hzPos
      have hNextUpper : cbrtStepNat x.val z ≤ 3 * 2 ^ 86 :=
        cbrtStepNat_le_three_pow86 x.val z hxLt haPos hFloor hUpper
      have hTail := ih
        (div (add (add (div x (mul zU zU)) zU) zU) 3)
        (cbrtStepNat x.val z) hStepVal hNextFloor hNextUpper
      simpa [cbrtIterUint, cbrtIterNat] using hTail

private theorem cbrtBeforeCorrectionUint_val_large
    (x : Uint256) (hx : 2 ^ 8 ≤ x.val) :
    (cbrtBeforeCorrectionUint x (cbrtScanSourceUint x)
      (cbrtSeedBaseUint x (cbrtScanSourceUint x))).val =
      soladyCbrtBeforeCorrectionNat x.val := by
  let seedU := cbrtFinishSeedUint x (cbrtScanSourceUint x)
    (cbrtSeedBaseUint x (cbrtScanSourceUint x))
  let seed := soladyCbrtSeedNat x.val
  let z1 := cbrtStepNat x.val seed
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hCbrtPos : 0 < natCbrt x.val := by
    have hGe : 6 ≤ natCbrt x.val := natCbrt_ge_six_of_ge_256 hx
    omega
  have hSeedVal : seedU.val = seed := by
    simpa [seedU, seed] using cbrtFinishSeedUint_val_large x hx
  have hSeedInfo := soladyCbrtSeedNat_real_bounds x.val hx hxLt
  have hSeedPos : 0 < seed := by simpa [seed] using hSeedInfo.1
  have hSeedUpper : seed ≤ 3 * 2 ^ 86 := by
    simpa [seed] using cbrtSeedNat_le_three_pow86 x.val hx hxLt
  have hSeedMulLt : seed * seed < Verity.Core.Uint256.modulus :=
    cbrt_square_no_overflow_of_le_three_pow86 hSeedUpper
  have hSeedAddLt :
      x.val / (seed * seed) + seed + seed < Verity.Core.Uint256.modulus := by
    simpa [seed] using cbrtSeedNat_add_no_overflow x.val hx hxLt
  have hStepVal :
      (div (add (add (div x (mul seedU seedU)) seedU) seedU) 3).val = z1 := by
    simpa [z1] using
      cbrtStepUint_val x seedU seed hSeedVal hSeedPos hSeedMulLt hSeedAddLt
  have hZ1Floor : natCbrt x.val ≤ z1 := by
    simpa [z1] using cbrtStepNat_ge_floor x.val seed hSeedPos
  have hZ1Upper : z1 ≤ 3 * 2 ^ 86 := by
    simpa [z1, seed] using cbrtSeedStepNat_le_three_pow86 x.val hx hxLt
  have hTail := cbrtIterUint_val_of_nat_floor 6 x
    (div (add (add (div x (mul seedU seedU)) seedU) seedU) 3) z1
    hxLt hCbrtPos hStepVal hZ1Floor hZ1Upper
  unfold cbrtBeforeCorrectionUint soladyCbrtBeforeCorrectionNat cbrtIterUint cbrtIterNat
  simpa [seedU, seed, z1] using hTail

private theorem cbrtFinishCorrectionUint_val
    (x zU : Uint256) (z : Nat)
    (hZVal : zU.val = z) (hzPos : 0 < z)
    (hMulLt : z * z < Verity.Core.Uint256.modulus) :
    (if div x (mul zU zU) < zU then sub zU 1 else zU).val =
      cbrtCorrectNat x.val z := by
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
  unfold cbrtCorrectNat
  by_cases h : x.val / (z * z) < z
  · have hUint := hBranchIff.mpr h
    rw [if_pos hUint, if_pos h]
    have hOne : (1 : Uint256).val = 1 := by simp
    have hSub : (sub zU 1).val = z - 1 := by
      have hLe : (1 : Uint256).val ≤ zU.val := by
        rw [hOne, hZVal]
        exact hzPos
      simpa [hZVal, hOne, HSub.hSub] using
        Verity.Core.Uint256.sub_eq_of_le (a := zU) (b := (1 : Uint256)) hLe
    exact hSub
  · have hUint : ¬ div x (mul zU zU) < zU := fun hh => h (hBranchIff.mp hh)
    rw [if_neg hUint, if_neg h]
    exact hZVal

private theorem cbrtFinishUint_val_large
    (x : Uint256) (hx : 2 ^ 8 ≤ x.val) :
    (cbrtFinishUint x (cbrtScanSourceUint x)
      (cbrtSeedBaseUint x (cbrtScanSourceUint x))).val =
      soladyCbrtNat x.val := by
  have hZVal :
      (cbrtBeforeCorrectionUint x (cbrtScanSourceUint x)
        (cbrtSeedBaseUint x (cbrtScanSourceUint x))).val =
        soladyCbrtBeforeCorrectionNat x.val :=
    cbrtBeforeCorrectionUint_val_large x hx
  have hxLt : x.val < 2 ^ 256 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt
  have hNear := soladyCbrtBeforeCorrectionNat_near_floor x.val hx hxLt
  have hzPos : 0 < soladyCbrtBeforeCorrectionNat x.val := by
    have haGe : 6 ≤ natCbrt x.val := natCbrt_ge_six_of_ge_256 hx
    exact lt_of_lt_of_le (by omega : 0 < natCbrt x.val) hNear.1
  have hZUpper : soladyCbrtBeforeCorrectionNat x.val ≤ 3 * 2 ^ 86 := by
    have hCbrtLt := natCbrt_lt_pow86 (x := x.val) hxLt
    omega
  have hMulLt :
      soladyCbrtBeforeCorrectionNat x.val *
          soladyCbrtBeforeCorrectionNat x.val <
        Verity.Core.Uint256.modulus :=
    cbrt_square_no_overflow_of_le_three_pow86 hZUpper
  simpa [cbrtFinishUint, soladyCbrtNat] using
    cbrtFinishCorrectionUint_val x
      (cbrtBeforeCorrectionUint x (cbrtScanSourceUint x)
        (cbrtSeedBaseUint x (cbrtScanSourceUint x)))
      (soladyCbrtBeforeCorrectionNat x.val) hZVal hzPos hMulLt

private theorem soladyCbrt_run_eq_model (x : Uint256) (s : ContractState) :
    ((cbrt x).run s).fst.val = soladyCbrtNat x.val := by
  rw [cbrt_run_eq_sourceUint x s]
  by_cases hxSmall : x.val < 256
  · have hxEq : x = uintOfNat x.val := by
      apply Verity.Core.Uint256.ext
      have hLt : x.val < Verity.Core.Uint256.modulus := x.isLt
      simp [uintOfNat_val_of_lt hLt]
    rw [hxEq]
    simpa [uintOfNat_val_of_lt x.isLt] using
      cbrtSourceUint_val_small ⟨x.val, hxSmall⟩
  · have hxLarge : 2 ^ 8 ≤ x.val := by
      norm_num at hxSmall
      omega
    simpa [cbrtSourceUint_eq_finishScan x] using cbrtFinishUint_val_large x hxLarge

theorem cbrt_returns_math_floor (x : Uint256) (s : ContractState) :
    cbrt_property x ((cbrt x).run s).fst := by
  unfold cbrt_property
  rw [soladyCbrt_run_eq_model x s]
  exact soladyCbrtNat_property x.val (by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt)

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
            hNatRound, hAdd, hAddRound]
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
      convert lower_of (k := 4) (by norm_num at h4 ⊢; omega) using 1 <;> omega
    · convert upper_of (k := 5) (by norm_num at hBound ⊢; omega) using 1 <;> omega
  · by_cases h3 : 999 < value
    · have h1 : 9 < value := by omega
      have h2 : 99 < value := by omega
      simp [log10Final, h1, h2, h3, h4]
      constructor
      · intro _hn
        convert lower_of (k := 3) (by norm_num at h3 ⊢; omega) using 1 <;> omega
      · convert upper_of (k := 4) (by norm_num at h4 ⊢; omega) using 1 <;> omega
    · by_cases h2 : 99 < value
      · have h1 : 9 < value := by omega
        simp [log10Final, h1, h2, h3, h4]
        constructor
        · intro _hn
          convert lower_of (k := 2) (by norm_num at h2 ⊢; omega) using 1 <;> omega
        · convert upper_of (k := 3) (by norm_num at h3 ⊢; omega) using 1 <;> omega
      · by_cases h1 : 9 < value
        · simp [log10Final, h1, h2, h3, h4]
          constructor
          · intro _hn
            convert lower_of (k := 1) (by norm_num at h1 ⊢; omega) using 1 <;> omega
          · convert upper_of (k := 2) (by norm_num at h2 ⊢; omega) using 1 <;> omega
        · simp [log10Final, h1, h2, h3, h4]
          constructor
          · exact hLower
          · convert upper_of (k := 1) (by norm_num at h1 ⊢; omega) using 1 <;> omega

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
    log10FinalContract3, Contract.run, Bind.bind, Pure.pure, Verity.pure,
    bind_pure_contract]
  split_ifs <;> simp [Contract.run, Pure.pure, Verity.pure, ContractResult.fst]

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
            bind_pure_contract,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd1, hAdd2,
            hAdd3, hAdd4]
        · have hn4 : ¬ 9999 < value.val := by simpa [h9999Val] using h4
          simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            bind_pure_contract,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd1, hAdd2,
            hAdd3]
      · have hn3 : ¬ 999 < value.val := by simpa [h999Val] using h3
        have hn4 : ¬ 9999 < value.val := by omega
        by_cases h4 : (uintOfNat 9999).val < value.val
        · have hn4' : 9999 < value.val := by simpa [h9999Val] using h4
          exact False.elim (hn4 hn4')
        · simp [log10FinalContract, log10FinalContract1, log10FinalContract2,
            log10FinalContract3, log10Final, Contract.run, Bind.bind, Pure.pure,
            bind_pure_contract,
            Verity.pure, h1, h2, h3, h4, hn1, hn2, hn3, hn4, hAdd1, hAdd2]
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
            bind_pure_contract,
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
            bind_pure_contract,
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
    simp only [log10SearchContract1, log10Search1, log10Search0, hBranch,
      hNatBranch, if_true]
    simpa [log10SearchContract0, hAdd, hDiv, hNatBranch, hNatBranchRaw] using hFinal
  · have hValBranch : ¬ (uintOfNat (10 ^ 5 - 1)).val < value.val := by
      simpa using hBranch
    have hNatBranch : ¬ 99999 < value.val := by simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 5 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hFinal := log10FinalContract_val r value s (by omega)
    simp only [log10SearchContract1, log10Search1, log10Search0, hBranch,
      hNatBranch, if_false]
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
    simp only [log10SearchContract2, log10Search2, hBranch, hNatBranch, if_true]
    simpa [hAdd, hDiv, hNatBranch, hNatBranchRaw] using hRec
  · have hValBranch : ¬ (uintOfNat (10 ^ 10 - 1)).val < value.val := by
      simpa using hBranch
    have hNatBranch : ¬ 9999999999 < value.val := by simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 10 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hRec := log10SearchContract1_val r value s (by omega)
    simp only [log10SearchContract2, log10Search2, hBranch, hNatBranch, if_false]
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
    simp only [log10SearchContract3, log10Search3, hBranch, hNatBranch, if_true]
    simpa [hAdd, hDiv, hNatBranch, hNatBranchRaw] using hRec
  · have hNatBranch : ¬ 99999999999999999999 < value.val := by
      have hValBranch : ¬ (uintOfNat (10 ^ 20 - 1)).val < value.val := by
        simpa using hBranch
      simpa [hThresholdVal] using hValBranch
    have hNatBranchRaw : ¬ 10 ^ 20 - 1 < value.val := by
      norm_num at hNatBranch ⊢
      exact hNatBranch
    have hRec := log10SearchContract2_val r value s (by omega)
    simp only [log10SearchContract3, log10Search3, hBranch, hNatBranch, if_false]
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
    simp only [log10SearchContract4, log10Search4, hBranch, hNatBranch, if_true]
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
    simp only [log10SearchContract4, log10Search4, hBranch, hNatBranch, if_false]
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
      · simp [hBranch, Bind.bind, Pure.pure, bind_pure_contract]
      · simp [hBranch, Bind.bind, Pure.pure, bind_pure_contract]
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
  simp only [ContractResult.fst_success]
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
  split_ifs <;> simp [Verity.pure, Contract.run, ContractResult.fst]

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
      Tamago.Utils.FixedPointMathLibBase.log256, Contract.run, Bind.bind,
      Pure.pure, Verity.pure]
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
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMaxChoosesMin, hMinAboveMax]
      · intro hValid
        exact False.elim (by omega)
      · intro hRange
        exact False.elim (by omega)
      · intro hLow
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMaxChoosesMin, hMinAboveMax]
    · have hValid : minValue.val ≤ maxValue.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        exact False.elim (hInvalid h)
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMaxChoosesMin, hValid]
      · intro hRange
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMaxChoosesMin, hValid]
      · intro hAbove
        exact False.elim (by omega)
  · have hMinLeX : minValue.val ≤ x.val := by omega
    by_cases hAbove : maxValue.val < x.val
    · have hXAboveMax : ¬ x.val ≤ maxValue.val := Nat.not_le_of_gt hAbove
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMinLeX, hXAboveMax]
      · intro hValid
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMinLeX, hXAboveMax]
        exact hValid
      · intro hRange
        exact False.elim (by omega)
      · intro hLow
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMinLeX, hXAboveMax]
    · have hXLeMax : x.val ≤ maxValue.val := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hInvalid
        exact False.elim (by omega)
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMinLeX, hXLeMax]
      · intro _h
        simp [clamp, Contract.run, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, hMinLeX, hXLeMax]
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
  simp [fixedPointMathLib_log2_zero_returns_zero, log2, Contract.run,
    Tamago.Utils.FixedPointMathLibBase.log2, Tamago.Utils.FixedPointMathLibBase.log256,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, shl, shr,
    Verity.Core.Uint256.shl, Verity.Core.Uint256.shr, Verity.Core.Uint256.ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

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
  simp [fixedPointMathLib_log2Up_zero_returns_zero, log2Up, Contract.run,
    Tamago.Utils.FixedPointMathLibBase.log2Up, Tamago.Utils.FixedPointMathLibBase.log2,
    Tamago.Utils.FixedPointMathLibBase.log256, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, shl, shr, Verity.Core.Uint256.shl, Verity.Core.Uint256.shr,
    Verity.Core.Uint256.ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

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
  simp [fixedPointMathLib_log10_zero_returns_zero, log10, Contract.run,
    Tamago.Utils.FixedPointMathLibBase.log10, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure]

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
  simp [fixedPointMathLib_log10Up_zero_returns_zero, log10Up, Contract.run,
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
  simp [fixedPointMathLib_log256_zero_returns_zero, log256, Contract.run,
    Tamago.Utils.FixedPointMathLibBase.log256, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure]

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
  simp [fixedPointMathLib_log256Up_zero_returns_zero, log256Up, Contract.run,
    Tamago.Utils.FixedPointMathLibBase.log256Up, Tamago.Utils.FixedPointMathLibBase.log256,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

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
