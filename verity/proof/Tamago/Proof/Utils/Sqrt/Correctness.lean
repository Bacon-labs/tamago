/-
  Correctness of `floorSqrt` on the uint256 domain.

  Combines the floor correction with the certificate-backed bounds
  to prove: for every x < 2^256, floorSqrt(x) satisfies the integer-sqrt spec.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Tamago.Proof.Utils.Sqrt.Wiring

namespace Tamago.Proof.Utils.Sqrt.Correctness

open Tamago.Proof.Utils.Sqrt.Model
open Tamago.Proof.Utils.Sqrt.FloorBound
open Tamago.Proof.Utils.Sqrt.OctaveCert
open Tamago.Proof.Utils.Sqrt.Wiring

-- ============================================================================
-- Floor Correction
-- ============================================================================

/-- The floor correction is correct.
    Given z > 0, (z-1)² ≤ x < (z+1)², subtracting the comparison flag
    `x/z < z` gives isqrt(x). -/
theorem floor_correction (x z : Nat) (hz : 0 < z)
    (hlo : (z - 1) * (z - 1) ≤ x)
    (hhi : x < (z + 1) * (z + 1)) :
    let r := z - if x / z < z then 1 else 0
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  simp only
  by_cases h_lt : x / z < z
  · simp [h_lt]
    have h_zsq : x < z * z := by
      have h_euc := Nat.div_add_mod x z
      have h_mod := Nat.mod_lt x hz
      have h1 : x < z * (x / z + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left z (by omega))
    constructor
    · exact hlo
    · have : z - 1 + 1 = z := by omega
      rw [this]; exact h_zsq
  · simp [h_lt]
    simp only [Nat.not_lt] at h_lt
    have h_zsq : z * z ≤ x := by
      calc z * z ≤ z * (x / z) := Nat.mul_le_mul_left z h_lt
        _ ≤ x := Nat.mul_div_le x z
    exact ⟨h_zsq, hhi⟩

-- ============================================================================
-- Universal Theorems
-- ============================================================================

/-- Correction-step correctness under a 1-ULP bracket
    for the inner approximation. -/
private theorem floorSqrt_correct (x : Nat) (hz : 0 < innerSqrt x)
    (hlo : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ x)
    (hhi : x < (innerSqrt x + 1) * (innerSqrt x + 1)) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  unfold floorSqrt
  simpa [Nat.ne_of_gt hz] using floor_correction x (innerSqrt x) hz hlo hhi

/-- End-to-end correction from the finite certificate assumptions. -/
private theorem floorSqrt_correct_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = seedOf i)
    (hlo : loOf i ≤ m)
    (hhi : m ≤ hiOf i) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  have hlow : m ≤ innerSqrt x := innerSqrt_lower x m hx hmlo
  have hupp : innerSqrt x ≤ m + 1 := innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hlo hhi
  have hz : 0 < innerSqrt x := Nat.lt_of_lt_of_le hm hlow
  have hlo' : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ x := by
    have hz1 : innerSqrt x - 1 ≤ m := by omega
    have hsq : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ m * m := Nat.mul_le_mul hz1 hz1
    exact Nat.le_trans hsq hmlo
  have hhi' : x < (innerSqrt x + 1) * (innerSqrt x + 1) := by
    have hm1 : m + 1 ≤ innerSqrt x + 1 := by omega
    have hsq : (m + 1) * (m + 1) ≤ (innerSqrt x + 1) * (innerSqrt x + 1) :=
      Nat.mul_le_mul hm1 hm1
    exact Nat.lt_of_lt_of_le hmhi hsq
  exact floorSqrt_correct x hz hlo' hhi'

/-- End-to-end correctness under octave membership. -/
private theorem floorSqrt_correct_of_octave
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
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
  exact floorSqrt_correct_cert i x m hx hm hmlo hmhi hseed hinterval.1 hinterval.2

/-- Universal `sqrt` correctness on uint256 domain (Nat model):
    for every `x < 2^256`, `floorSqrt x` satisfies the integer-sqrt spec. -/
theorem floorSqrt_correct_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [floorSqrt, innerSqrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    let i : Fin 256 := ⟨Nat.log2 x, (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256⟩
    let m := Nat.sqrt x
    have hmlo : m * m ≤ x := by simpa [m] using Nat.sqrt_le x
    have hmhi : x < (m + 1) * (m + 1) := by simpa [m] using Nat.lt_succ_sqrt x
    have hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1) := by
      have hlog : 2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) := by
        constructor
        · simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.ne_of_gt hx)
        · simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
            Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
      simpa [i]
    exact floorSqrt_correct_of_octave i x m hmlo hmhi hOct

end Tamago.Proof.Utils.Sqrt.Correctness
