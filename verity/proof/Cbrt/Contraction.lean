/-
  One-step contraction for the cube root Newton-Raphson iteration.

  Proves that if z = m + d with 2d ≤ m, one NR step contracts
  the error: cbrtStep x z ≤ m + d²/m + 1.
-/
import Init
import Cbrt.Model
import Cbrt.FloorBound

namespace Cbrt.Contraction

open Cbrt.Model
open Cbrt.FloorBound

-- ============================================================================
-- Seed and Step Positivity
-- ============================================================================

/-- The cbrt seed is always positive (due to the low-bit OR). -/
theorem cbrtSeed_pos (x : Nat) : 0 < cbrtSeed x := by
  unfold cbrtSeed
  have h : 1 ≤ 1 ||| ((cbrtSeedMultiplier (Nat.log2 x) <<< (Nat.log2 x / 3)) >>> 7) :=
    Nat.left_le_or
  omega

/-- cbrtStep preserves positivity when x > 0 and z > 0. -/
theorem cbrtStep_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) : 0 < cbrtStep x z := by
  unfold cbrtStep
  -- Numerator = x/(z*z) + 2*z ≥ 2*z ≥ 2.
  -- For z = 1: numerator = x + 2 ≥ 3, so /3 ≥ 1.
  -- For z ≥ 2: numerator ≥ 4, so /3 ≥ 1.
  have hzz : 0 < z * z := Nat.mul_pos hz hz
  by_cases h : z = 1
  · -- z = 1: numerator = x/1 + 2 = x + 2 ≥ 3, so /3 ≥ 1
    subst h; simp
    -- goal: 0 < (x / 1 + 2) / 3 or similar. omega handles.
    omega
  · -- z ≥ 2: numerator ≥ 0 + 2z ≥ 4, so /3 ≥ 1
    have hz2 : z ≥ 2 := by omega
    -- x/(z*z) is a Nat ≥ 0. 2*z ≥ 4. Sum ≥ 4. 4/3 = 1 > 0.
    have h_num_ge : x / (z * z) + 2 * z ≥ 3 := by
      have : 2 * z ≥ 4 := by omega
      have : x / (z * z) ≥ 0 := Nat.zero_le _
      omega
    omega

-- ============================================================================
-- One-Step Upper Bound
-- ============================================================================

/-- Integer polynomial identity used to upper-bound one cbrt Newton step. -/
private theorem pullCoeff (x y c : Int) : x * (y * c) = c * (x * y) := by
  rw [← Int.mul_assoc x y c]
  rw [Int.mul_comm (x * y) c]

private theorem pullCoeffNested (x y z c : Int) : x * (y * (z * c)) = c * (x * (y * z)) := by
  rw [← Int.mul_assoc y z c]
  rw [pullCoeff x (y * z) c]

private theorem int_poly_identity (m d q r : Int)
    (hd2 : d * d = m * q + r) :
    ((m - 2 * d + 3 * q + 6) * ((m + d) * (m + d)) - (m + 1) * (m + 1) * (m + 1))
      =
    q * (3 * m * q + 6 * m + 3 * r + 4 * d * m)
      + (-2 * d * r + 12 * d * m + 3 * m * m - 3 * m * r - 3 * m + 6 * r - 1) := by
  simp [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  repeat rw [Int.mul_neg]
  repeat rw [Int.neg_mul]
  have hddx (x : Int) : d * (d * x) = (d * d) * x := by
    rw [← Int.mul_assoc]
  simp [hddx, hd2, Int.add_mul, Int.mul_add,
    Int.mul_assoc, Int.mul_left_comm]
  -- Normalize monomials with numeric coefficients.
  rw [pullCoeffNested m m d 2]
  rw [pullCoeffNested m m q 2]
  rw [pullCoeff m r 2]
  rw [pullCoeffNested m d q 2]
  rw [pullCoeff d r 2]
  rw [pullCoeffNested m m q 3]
  rw [pullCoeffNested m d q 3]
  rw [pullCoeff m m 6]
  rw [pullCoeff m d 6]
  rw [pullCoeff m q 6]
  rw [pullCoeff m d 12]
  rw [pullCoeffNested m d q 4]
  rw [pullCoeff m r 3]
  rw [pullCoeff m m 3]
  -- Collapse the expanded `(m + 1)^3` chunk.
  have hcube :
      m * (m * m) + m * m + (m * m + m) + (m * m + m + (m + 1))
        = m * (m * m) + 3 * (m * m) + 3 * m + 1 := by
    omega
  rw [hcube]
  omega

private theorem neg3_mul_mul (m r : Int) : -3 * m * r = -(3 * m * r) := by
  calc
    -3 * m * r = (-3 * m) * r := by rw [Int.mul_assoc]
    _ = (-(3 * m)) * r := by rw [Int.neg_mul]
    _ = -(3 * m * r) := by rw [Int.neg_mul, Int.mul_assoc]

private theorem mul_coeff_expand (m d r : Int) :
    r * (-2 * d - 3 * m + 6) = -2 * d * r - 3 * m * r + 6 * r := by
  rw [Int.mul_add]
  have hsum : -2 * d - 3 * m = (-2 * d) + (-3 * m) := by omega
  rw [hsum, Int.mul_add]
  rw [Int.mul_comm r (-2 * d), Int.mul_comm r (-3 * m), Int.mul_comm r 6]
  repeat rw [Int.sub_eq_add_neg]
  rw [neg3_mul_mul]

/-- Product form of the one-step upper bound (core arithmetic bridge). -/
private theorem one_step_prod_bound (m d : Nat) (hm2 : 2 ≤ m) :
    (m + 1) * (m + 1) * (m + 1) ≤
      (m - 2 * d + 3 * (d * d / m) + 6) * ((m + d) * (m + d)) := by
  let q : Nat := d * d / m
  let r : Nat := d * d % m
  have hm : 0 < m := by omega
  have hr : r < m := by
    dsimp [r]
    exact Nat.mod_lt _ hm
  have hd2 : d * d = m * q + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod (d * d) m).symm

  have hd2i : (d : Int) * (d : Int) = (m : Int) * (q : Int) + (r : Int) := by
    exact_mod_cast hd2

  have hEqInt :
      (((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6) *
          (((m : Int) + (d : Int)) * ((m : Int) + (d : Int)))
        - ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1))
      =
      (q : Int) * (3 * (m : Int) * (q : Int) + 6 * (m : Int) + 3 * (r : Int) + 4 * (d : Int) * (m : Int))
        + (-2 * (d : Int) * (r : Int) + 12 * (d : Int) * (m : Int)
            + 3 * (m : Int) * (m : Int) - 3 * (m : Int) * (r : Int)
            - 3 * (m : Int) + 6 * (r : Int) - 1) := by
    exact int_poly_identity (m := (m : Int)) (d := (d : Int)) (q := (q : Int)) (r := (r : Int)) hd2i

  have hm_nonneg : 0 ≤ (m : Int) := Int.natCast_nonneg m
  have hq_nonneg : 0 ≤ (q : Int) := Int.natCast_nonneg q
  have hr_nonneg : 0 ≤ (r : Int) := Int.natCast_nonneg r
  have hd_nonneg : 0 ≤ (d : Int) := Int.natCast_nonneg d

  have h3_nonneg : (0 : Int) ≤ 3 := by decide
  have h4_nonneg : (0 : Int) ≤ 4 := by decide
  have h6_nonneg : (0 : Int) ≤ 6 := by decide
  have h10_nonneg : (0 : Int) ≤ 10 := by decide
  have h2_nonneg : (0 : Int) ≤ 2 := by decide

  have h3m_nonneg : 0 ≤ 3 * (m : Int) := Int.mul_nonneg h3_nonneg hm_nonneg
  have h6m_nonneg : 0 ≤ 6 * (m : Int) := Int.mul_nonneg h6_nonneg hm_nonneg
  have h3r_nonneg : 0 ≤ 3 * (r : Int) := Int.mul_nonneg h3_nonneg hr_nonneg
  have h4d_nonneg : 0 ≤ 4 * (d : Int) := Int.mul_nonneg h4_nonneg hd_nonneg

  have h1_nonneg : 0 ≤ 3 * (m : Int) * (q : Int) := Int.mul_nonneg h3m_nonneg hq_nonneg
  have h4_nonneg' : 0 ≤ 4 * (d : Int) * (m : Int) := Int.mul_nonneg h4d_nonneg hm_nonneg

  have hfac_nonneg : 0 ≤ 3 * (m : Int) * (q : Int) + 6 * (m : Int) + 3 * (r : Int) + 4 * (d : Int) * (m : Int) := by
    omega

  have hQ_nonneg :
      0 ≤ (q : Int) * (3 * (m : Int) * (q : Int) + 6 * (m : Int) + 3 * (r : Int) + 4 * (d : Int) * (m : Int)) := by
    exact Int.mul_nonneg hq_nonneg hfac_nonneg

  have hc_nonpos : -2 * (d : Int) - 3 * (m : Int) + 6 ≤ 0 := by
    have hm_ge_two : (2 : Int) ≤ (m : Int) := by exact_mod_cast hm2
    omega

  have hr_le : (r : Int) ≤ ((m - 1 : Nat) : Int) := by
    have : r ≤ m - 1 := by omega
    exact Int.ofNat_le.mpr this

  have h_mul_lower :
      ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
        ≤ (r : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
    exact Int.mul_le_mul_of_nonpos_right hr_le hc_nonpos

  have h_rewrite :
      (-2 * (d : Int) * (r : Int) + 12 * (d : Int) * (m : Int)
        + 3 * (m : Int) * (m : Int) - 3 * (m : Int) * (r : Int)
        - 3 * (m : Int) + 6 * (r : Int) - 1)
      = (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
        + (r : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
    rw [mul_coeff_expand (m := (m : Int)) (d := (d : Int)) (r := (r : Int))]
    repeat rw [Int.sub_eq_add_neg]
    ac_rfl

  have h_rewrite0 :
      (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
        + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
      = 10 * (d : Int) * (m : Int) + 2 * (d : Int) + 6 * (m : Int) - 7 := by
    have hm1 : 1 ≤ m := Nat.le_trans (by decide : 1 ≤ 2) hm2
    have ht : ((m - 1 : Nat) : Int) = (m : Int) - 1 := by omega
    rw [ht, Int.sub_mul, Int.one_mul]
    rw [mul_coeff_expand (m := (m : Int)) (d := (d : Int)) (r := (m : Int))]
    repeat rw [Int.sub_eq_add_neg]
    have hneg : -(-2 * (d : Int) + -(3 * (m : Int)) + 6) = 2 * (d : Int) + 3 * (m : Int) - 6 := by
      omega
    rw [hneg]
    rw [Int.mul_assoc 12 (d : Int) (m : Int)]
    rw [Int.mul_assoc (-2) (d : Int) (m : Int)]
    rw [Int.mul_assoc 10 (d : Int) (m : Int)]
    rw [Int.mul_assoc 3 (m : Int) (m : Int)]
    omega

  have h10dm_nonneg : 0 ≤ 10 * (d : Int) * (m : Int) := by
    have h10d_nonneg : 0 ≤ 10 * (d : Int) := Int.mul_nonneg h10_nonneg hd_nonneg
    exact Int.mul_nonneg h10d_nonneg hm_nonneg
  have h2d_nonneg : 0 ≤ 2 * (d : Int) := Int.mul_nonneg h2_nonneg hd_nonneg
  have h6m_minus7_nonneg : 0 ≤ 6 * (m : Int) - 7 := by
    have hm_ge_two : (2 : Int) ≤ (m : Int) := by exact_mod_cast hm2
    omega

  have h0 :
      0 ≤ (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
            + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
    rw [h_rewrite0]
    omega

  have hLin :
      0 ≤ (-2 * (d : Int) * (r : Int) + 12 * (d : Int) * (m : Int)
            + 3 * (m : Int) * (m : Int) - 3 * (m : Int) * (r : Int)
            - 3 * (m : Int) + 6 * (r : Int) - 1) := by
    rw [h_rewrite]
    have h_add :
        (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
          + ((m - 1 : Nat) : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6)
        ≤
        (12 * (d : Int) * (m : Int) + 3 * (m : Int) * (m : Int) - 3 * (m : Int) - 1)
          + (r : Int) * (-2 * (d : Int) - 3 * (m : Int) + 6) := by
      exact Int.add_le_add_left h_mul_lower _
    exact Int.le_trans h0 h_add

  have hdiff_nonneg :
      0 ≤ (((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6) *
              (((m : Int) + (d : Int)) * ((m : Int) + (d : Int)))
            - ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1)) := by
    rw [hEqInt]
    exact Int.add_nonneg hQ_nonneg hLin

  have hIntMain :
      ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1) ≤
        ((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6) *
          (((m : Int) + (d : Int)) * ((m : Int) + (d : Int))) := by
    omega

  have hCoeffLe :
      ((m : Int) - 2 * (d : Int) + 3 * (q : Int) + 6)
        ≤ ((m - 2 * d + 3 * q + 6 : Nat) : Int) := by
    omega

  have hz_nonneg : 0 ≤ (((m : Int) + (d : Int)) * ((m : Int) + (d : Int))) := by
    have : 0 ≤ (m : Int) + (d : Int) := Int.add_nonneg hm_nonneg hd_nonneg
    exact Int.mul_nonneg this this

  have hIntNatCoeff :
      ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1)
        ≤ ((m - 2 * d + 3 * q + 6 : Nat) : Int) *
            (((m : Int) + (d : Int)) * ((m : Int) + (d : Int))) := by
    exact Int.le_trans hIntMain (Int.mul_le_mul_of_nonneg_right hCoeffLe hz_nonneg)

  exact_mod_cast hIntNatCoeff

/-- Division form of the one-step upper bound. -/
private theorem one_step_div_bound (m d : Nat) (hm2 : 2 ≤ m) :
    (((m + 1) * (m + 1) * (m + 1) - 1) / ((m + d) * (m + d)))
      ≤ m - 2 * d + 3 * (d * d / m) + 5 := by
  let A : Nat := m - 2 * d + 3 * (d * d / m) + 5
  let B : Nat := (m + d) * (m + d)
  have hBpos : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hprod : (m + 1) * (m + 1) * (m + 1) ≤ (A + 1) * B := by
    dsimp [A, B]
    simpa [Nat.add_assoc] using one_step_prod_bound m d hm2
  have hpred : (m + 1) * (m + 1) * (m + 1) - 1 < (m + 1) * (m + 1) * (m + 1) := by
    have hpos : 0 < (m + 1) * (m + 1) * (m + 1) := by
      have hm1 : 0 < m + 1 := by omega
      exact Nat.mul_pos (Nat.mul_pos hm1 hm1) hm1
    exact Nat.sub_lt hpos (by omega)
  have hlt : (m + 1) * (m + 1) * (m + 1) - 1 < (A + 1) * B :=
    Nat.lt_of_lt_of_le hpred hprod
  have hdivlt : (((m + 1) * (m + 1) * (m + 1) - 1) / B) < A + 1 := by
    exact (Nat.div_lt_iff_lt_mul hBpos).2 hlt
  have hdivle : (((m + 1) * (m + 1) * (m + 1) - 1) / B) ≤ A := by
    exact Nat.lt_succ_iff.mp hdivlt
  simpa [A, B]

/-- If `x < (m+1)^3` and `z = m+d` with `2d ≤ m`, one cbrt step keeps
    the overestimate within `d^2/m + 1`. -/
private theorem cbrtStep_upper_of_delta
    (x m d : Nat)
    (hm2 : 2 ≤ m)
    (h2d : 2 * d ≤ m)
    (hx : x < (m + 1) * (m + 1) * (m + 1)) :
    cbrtStep x (m + d) ≤ m + (d * d / m) + 1 := by
  let q : Nat := d * d / m
  let z : Nat := m + d
  have hxle : x ≤ (m + 1) * (m + 1) * (m + 1) - 1 := by omega
  have hdiv_x : x / (z * z) ≤ ((m + 1) * (m + 1) * (m + 1) - 1) / (z * z) :=
    Nat.div_le_div_right hxle
  have hdiv_m :
      ((m + 1) * (m + 1) * (m + 1) - 1) / (z * z) ≤ m - 2 * d + 3 * q + 5 := by
    simpa [z, q, Nat.mul_assoc] using one_step_div_bound m d hm2
  have hdiv : x / (z * z) ≤ m - 2 * d + 3 * q + 5 := Nat.le_trans hdiv_x hdiv_m
  unfold cbrtStep
  have hsum : x / (z * z) + 2 * z ≤ (m - 2 * d + 3 * q + 5) + 2 * z := by
    exact Nat.add_le_add_right hdiv _
  have hdiv3 :
      (x / (z * z) + 2 * z) / 3
        ≤ ((m - 2 * d + 3 * q + 5) + 2 * z) / 3 :=
    Nat.div_le_div_right hsum
  have hfinal : ((m - 2 * d + 3 * q + 5) + 2 * z) / 3 ≤ m + q + 1 := by
    omega
  have hz : z = m + d := by rfl
  rw [hz] at hdiv3 hfinal
  simpa [q] using Nat.le_trans hdiv3 hfinal

/-- Upper-bound transfer form: if `z` is between `m` and `m+d`, one cbrt step is
    bounded by the same `d^2/m + 1` expression. -/
theorem cbrtStep_upper_of_le
    (x m z d : Nat)
    (hm2 : 2 ≤ m)
    (hmz : m ≤ z)
    (hzd : z ≤ m + d)
    (h2d : 2 * d ≤ m)
    (hx : x < (m + 1) * (m + 1) * (m + 1)) :
    cbrtStep x z ≤ m + (d * d / m) + 1 := by
  let d' : Nat := z - m
  have hz_eq : z = m + d' := by
    dsimp [d']
    omega
  have hd'_le : d' ≤ d := by
    dsimp [d']
    omega
  have h2d' : 2 * d' ≤ m := Nat.le_trans (Nat.mul_le_mul_left 2 hd'_le) h2d
  have hstep' : cbrtStep x z ≤ m + (d' * d' / m) + 1 := by
    rw [hz_eq]
    exact cbrtStep_upper_of_delta x m d' hm2 h2d' hx
  have hsq : d' * d' ≤ d * d := Nat.mul_le_mul hd'_le hd'_le
  have hdiv : d' * d' / m ≤ d * d / m := Nat.div_le_div_right hsq
  have hmono : m + (d' * d' / m) + 1 ≤ m + (d * d / m) + 1 := by
    exact Nat.add_le_add_left (Nat.add_le_add_right hdiv 1) m
  exact Nat.le_trans hstep' hmono


end Cbrt.Contraction
