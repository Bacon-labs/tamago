/-
  Wiring: connects the octave certificates and error chain to the
  concrete `innerSqrt` algorithm, establishing:
  - Seed and step positivity
  - Lower bound: m ≤ innerSqrt x for any m with m² ≤ x
  - Upper bound: innerSqrt x ≤ m + 1 via the finite certificate
  - Octave-to-certificate mapping
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Tamago.Proof.Utils.Sqrt.Model
import Tamago.Proof.Utils.Sqrt.FloorBound
import Tamago.Proof.Utils.Sqrt.ErrorChain

namespace Tamago.Proof.Utils.Sqrt.Wiring

open Tamago.Proof.Utils.Sqrt.Model
open Tamago.Proof.Utils.Sqrt.FloorBound
open Tamago.Proof.Utils.Sqrt.OctaveCert
open Tamago.Proof.Utils.Sqrt.ErrorChain

-- ============================================================================
-- Seed and Step Positivity
-- ============================================================================

/-- The seed is positive for x > 0. -/
theorem sqrtSeed_pos (x : Nat) (hx : 0 < x) :
    0 < sqrtSeed x := by
  unfold sqrtSeed
  simp [Nat.ne_of_gt hx]
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.lt_of_lt_of_le (by omega : 0 < 1) (Nat.one_le_pow _ 2 (by omega))

/-- sqrtStep preserves positivity when x > 0 and z > 0. -/
theorem sqrtStep_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) : 0 < sqrtStep x z := by
  unfold sqrtStep
  by_cases hle : x < z
  · have : x / z = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hle)
    omega
  · have : 0 < x / z := Nat.div_pos (by omega) hz
    omega

-- ============================================================================
-- Lower Bound
-- ============================================================================

/-- innerSqrt gives a lower bound: for any m with m² ≤ x, m ≤ innerSqrt(x). -/
theorem innerSqrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m ≤ x) : m ≤ innerSqrt x := by
  unfold innerSqrt
  simp [Nat.ne_of_gt hx]
  have hs := sqrtSeed_pos x hx
  have h1 := sqrtStep_pos x _ hx hs
  have h2 := sqrtStep_pos x _ hx h1
  have h3 := sqrtStep_pos x _ hx h2
  have h4 := sqrtStep_pos x _ hx h3
  have h5 := sqrtStep_pos x _ hx h4
  exact sqrt_step_floor_bound x _ m h5 hm

/-- Unfolding identity: `innerSqrt` is six steps starting from `sqrtSeed`. -/
theorem innerSqrt_eq_run6From (x : Nat) (hx : 0 < x) :
    innerSqrt x = run6From x (sqrtSeed x) := by
  unfold innerSqrt run6From
  simp [Nat.ne_of_gt hx, sqrtStep]

-- ============================================================================
-- Octave-to-Certificate Mapping
-- ============================================================================

/-- `sqrtSeed` agrees with the finite-certificate seed on octave `i`. -/
theorem sqrtSeed_eq_octaveSeed
    (i : Fin 256) (x : Nat)
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    sqrtSeed x = seedOf i := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hlog : Nat.log2 x = i.val := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_eq_iff (b := 2) (m := i.val) (n := x)
      (Or.inr ⟨by decide, hx0⟩)).2 hOct
  unfold sqrtSeed seedOf
  simp [Nat.ne_of_gt hx, hlog]

/-- From the certified octave endpoints and `m² ≤ x < (m+1)²`,
    derive `m ∈ [loOf i, hiOf i]`. -/
theorem m_within_cert_interval
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    loOf i ≤ m ∧ m ≤ hiOf i := by
  have hloSq : loOf i * loOf i ≤ 2 ^ i.val := lo_sq_le_pow2 i
  have hloSqX : loOf i * loOf i ≤ x := Nat.le_trans hloSq hOct.1
  have hlo : loOf i ≤ m := by
    by_cases h : loOf i ≤ m
    · exact h
    · have hlt : m < loOf i := Nat.lt_of_not_ge h
      have hm1 : m + 1 ≤ loOf i := Nat.succ_le_of_lt hlt
      have hm1sq : (m + 1) * (m + 1) ≤ loOf i * loOf i :=
        Nat.mul_le_mul hm1 hm1
      have hm1x : (m + 1) * (m + 1) ≤ x := Nat.le_trans hm1sq hloSqX
      exact False.elim ((Nat.not_lt_of_ge hm1x) hmhi)
  have hhiSq : 2 ^ (i.val + 1) ≤ (hiOf i + 1) * (hiOf i + 1) :=
    pow2_succ_le_hi_succ_sq i
  have hXHi : x < (hiOf i + 1) * (hiOf i + 1) :=
    Nat.lt_of_lt_of_le hOct.2 hhiSq
  have hhi : m ≤ hiOf i := by
    by_cases h : m ≤ hiOf i
    · exact h
    · have hlt : hiOf i < m := Nat.lt_of_not_ge h
      have hhi1 : hiOf i + 1 ≤ m := Nat.succ_le_of_lt hlt
      have hhimsq : (hiOf i + 1) * (hiOf i + 1) ≤ m * m :=
        Nat.mul_le_mul hhi1 hhi1
      have hXmm : x < m * m := Nat.lt_of_lt_of_le hXHi hhimsq
      exact False.elim ((Nat.not_lt_of_ge hmlo) hXmm)
  exact ⟨hlo, hhi⟩

-- ============================================================================
-- Upper Bound
-- ============================================================================

/-- Certificate-backed upper bound: six steps from the certificate seed
    satisfy `innerSqrt x ≤ m + 1`. -/
theorem innerSqrt_upper_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = seedOf i)
    (hlo : loOf i ≤ m)
    (hhi : m ≤ hiOf i) :
    innerSqrt x ≤ m + 1 := by
  have hrun : run6From x (seedOf i) ≤ m + 1 :=
    run6_le_m_plus_one i x m hm hmlo hmhi hlo hhi
  calc
    innerSqrt x = run6From x (sqrtSeed x) := innerSqrt_eq_run6From x hx
    _ = run6From x (seedOf i) := by simp [hseed]
    _ ≤ m + 1 := hrun

/-- Certificate-backed upper bound under octave membership. -/
theorem innerSqrt_upper_of_octave
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    innerSqrt x ≤ m + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  have hm : 0 < m := by
    by_cases hm0 : m = 0
    · subst hm0
      have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx
      have hlt1 : x < 1 := by simpa using hmhi
      exact False.elim ((Nat.not_lt_of_ge hx1) hlt1)
    · exact Nat.pos_of_ne_zero hm0
  have hseed : sqrtSeed x = seedOf i := sqrtSeed_eq_octaveSeed i x hOct
  have hinterval : loOf i ≤ m ∧ m ≤ hiOf i :=
    m_within_cert_interval i x m hmlo hmhi hOct
  exact innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hinterval.1 hinterval.2

end Tamago.Proof.Utils.Sqrt.Wiring
