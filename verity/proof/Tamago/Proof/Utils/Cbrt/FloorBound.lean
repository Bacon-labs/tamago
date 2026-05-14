/-
  Floor bound for the cube root Newton-Raphson step.

  For any m with m³ ≤ x, and z > 0:  m ≤ cbrtStep x z.

  A single truncated NR step for cube root never undershoots icbrt(x).
  Core inequality: (3m - 2z) * z² ≤ m³ (cubic AM-GM).
-/
import Init

namespace Tamago.Proof.Utils.Cbrt.FloorBound

-- ============================================================================
-- Algebraic Helpers
-- ============================================================================

/-- (d+z)³ = d³ + 3d²z + 3dz² + z³ (left-associated products). -/
private theorem cube_expand (d z : Nat) :
    (d + z) * (d + z) * (d + z) =
    d * d * d + 3 * (d * d * z) + 3 * (d * z * z) + z * z * z := by
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_assoc]
  simp only [Nat.mul_comm z d, Nat.mul_left_comm z d]
  omega

private theorem cubic_witness (d z : Nat) :
    (3 * d + z) * (z * z) + d * d * (d + 3 * z) = (d + z) * (d + z) * (d + z) := by
  rw [Nat.add_mul (3 * d) z (z * z)]
  rw [Nat.mul_add (d * d) d (3 * z)]
  rw [cube_expand d z]
  rw [Nat.mul_assoc 3 d (z * z)]
  rw [Nat.mul_comm (d * d) (3 * z), Nat.mul_assoc 3 z (d * d), Nat.mul_comm z (d * d)]
  simp only [Nat.mul_assoc]
  omega

-- ============================================================================
-- Cubic AM-GM
-- ============================================================================

theorem cubic_identity_le (z m : Nat) (h : z ≤ m) :
    (3 * m - 2 * z) * (z * z) + (m - z) * (m - z) * (m + 2 * z) = m * m * m := by
  have hd : 3 * m - 2 * z = 3 * (m - z) + z := by omega
  have hm2z : m + 2 * z = (m - z) + 3 * z := by omega
  rw [hd, hm2z]
  have key := cubic_witness (m - z) z
  rw [Nat.sub_add_cancel h] at key
  exact key

private theorem cubic_witness_ge (a b : Nat) :
    a * ((a + 3 * b) * (a + 3 * b)) + b * b * (3 * a + 8 * b) =
    (a + 2 * b) * (a + 2 * b) * (a + 2 * b) := by
  rw [show 3 * b = b + (b + b) from by omega]
  rw [show 3 * a = a + (a + a) from by omega]
  rw [show 8 * b = b + (b + (b + (b + (b + (b + (b + b)))))) from by omega]
  rw [show 2 * b = b + b from by omega]
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_assoc]
  simp only [Nat.mul_comm b a, Nat.mul_left_comm b a]
  omega

theorem cubic_identity_ge (z m : Nat) (h1 : m ≤ z) (h2 : 2 * z ≤ 3 * m) :
    (3 * m - 2 * z) * (z * z) + (z - m) * (z - m) * (m + 2 * z) = m * m * m := by
  have key := cubic_witness_ge (3 * m - 2 * z) (z - m)
  have h3 : 3 * m - 2 * z + 3 * (z - m) = z := by omega
  have h4 : 3 * (3 * m - 2 * z) + 8 * (z - m) = m + 2 * z := by omega
  have h5 : 3 * m - 2 * z + 2 * (z - m) = m := by omega
  rw [h3, h4, h5] at key
  exact key

theorem cubic_am_gm (z m : Nat) : (3 * m - 2 * z) * (z * z) ≤ m * m * m := by
  by_cases h : z ≤ m
  · have := cubic_identity_le z m h; omega
  · simp only [Nat.not_le] at h
    by_cases h2 : 2 * z ≤ 3 * m
    · have := cubic_identity_ge z m (Nat.le_of_lt h) h2; omega
    · simp only [Nat.not_le] at h2
      simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt h2)]

-- ============================================================================
-- Floor Bound
-- ============================================================================

/--
**Floor Bound for cube root Newton-Raphson.**

For any `m` with `m³ ≤ x`, and `z > 0`:
    m ≤ (x / (z * z) + 2 * z) / 3

A single truncated NR step for cube root never undershoots `icbrt(x)`.
-/
theorem cbrt_step_floor_bound (x z m : Nat) (hz : 0 < z) (hm : m * m * m ≤ x) :
    m ≤ (x / (z * z) + 2 * z) / 3 := by
  have hzz : 0 < z * z := Nat.mul_pos hz hz
  rw [Nat.le_div_iff_mul_le (by omega : (0 : Nat) < 3)]
  suffices h : 3 * m - 2 * z ≤ x / (z * z) by omega
  rw [Nat.le_div_iff_mul_le hzz]
  calc (3 * m - 2 * z) * (z * z)
      ≤ m * m * m := cubic_am_gm z m
    _ ≤ x := hm

end Tamago.Proof.Utils.Cbrt.FloorBound
