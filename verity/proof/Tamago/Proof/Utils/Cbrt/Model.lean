/-
  Nat model of the optimized cube-root algorithm, plus a reference
  integer cube root (`icbrt`) with full floor specification.
-/
import Init

namespace Tamago.Proof.Utils.Cbrt.Model

-- ============================================================================
-- Definitions
-- ============================================================================

/-- One Newton-Raphson step for cube root: ⌊(⌊x/z²⌋ + 2z) / 3⌋.
    Matches EVM: div(add(add(div(x, mul(z, z)), z), z), 3) -/
def cbrtStep (x z : Nat) : Nat := (x / (z * z) + 2 * z) / 3

/-- Fixed-point multiplier selected by `log2(x) % 3`. -/
def cbrtSeedMultiplier (y : Nat) : Nat :=
  #[0x90, 0xb5, 0xe5][y % 3]!

/-- The cbrt seed:
    z = (⌊c * 2^q / 128⌋ | 1) where y = log2(x), q = ⌊y / 3⌋, and
    c is selected from [0x90, 0xb5, 0xe5] by y % 3. -/
def cbrtSeed (x : Nat) : Nat :=
  1 ||| ((cbrtSeedMultiplier (Nat.log2 x) <<< (Nat.log2 x / 3)) >>> 7)

/-- innerCbrt: seed + 5 Newton-Raphson steps. -/
def innerCbrt (x : Nat) : Nat :=
  let z := cbrtSeed x
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- floorCbrt: innerCbrt with floor correction.
    Matches EVM: z := sub(z, lt(div(x, mul(z, z)), z)) -/
def floorCbrt (x : Nat) : Nat :=
  let z := innerCbrt x
  z - if x / (z * z) < z then 1 else 0

-- ============================================================================
-- Iteration Helpers
-- ============================================================================

/-- Run five cbrt Newton steps from an explicit starting point. -/
def run5From (x z : Nat) : Nat :=
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- Run four cbrt Newton steps from an explicit starting point. -/
def run4From (x z : Nat) : Nat :=
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  let z := cbrtStep x z
  z

/-- run5From = cbrtStep after run4From (definitional). -/
theorem run5_eq_step_run4 (x z : Nat) :
    run5From x z = cbrtStep x (run4From x z) := rfl

/-- innerCbrt is exactly run5From from the seed (definitional). -/
theorem innerCbrt_eq_run5From_seed (x : Nat) :
    innerCbrt x = run5From x (cbrtSeed x) := rfl

/-- innerCbrt is cbrtStep applied to run4From of the seed (definitional). -/
theorem innerCbrt_eq_step_run4_seed (x : Nat) :
    innerCbrt x = cbrtStep x (run4From x (cbrtSeed x)) := rfl

-- ============================================================================
-- Reference Integer Cube Root
-- ============================================================================

/-- Search helper: largest `m ≤ n` such that `m^3 ≤ x`. -/
def icbrtAux (x n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => if (n + 1) * (n + 1) * (n + 1) ≤ x then n + 1 else icbrtAux x n

/-- Reference integer cube root (floor). -/
def icbrt (x : Nat) : Nat :=
  icbrtAux x x

theorem cube_monotone {a b : Nat} (h : a ≤ b) :
    a * a * a ≤ b * b * b := by
  have h1 : a * a * a ≤ b * a * a := by
    have hmul : a * a ≤ b * a := Nat.mul_le_mul_right a h
    exact Nat.mul_le_mul_right a hmul
  have h2 : b * a * a ≤ b * b * a := by
    have hmul : b * a ≤ b * b := Nat.mul_le_mul_left b h
    exact Nat.mul_le_mul_right a hmul
  have h3 : b * b * a ≤ b * b * b := by
    exact Nat.mul_le_mul_left (b * b) h
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

private theorem le_cube_of_pos {a : Nat} (ha : 0 < a) :
    a ≤ a * a * a := by
  have h1 : 1 ≤ a := Nat.succ_le_of_lt ha
  have h2 : a ≤ a * a := by
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left a h1)
  have h3 : a * a ≤ a * a * a := by
    simpa [Nat.mul_one, Nat.mul_assoc] using (Nat.mul_le_mul_left (a * a) h1)
  exact Nat.le_trans h2 h3

private theorem icbrtAux_cube_le (x n : Nat) :
    icbrtAux x n * icbrtAux x n * icbrtAux x n ≤ x := by
  induction n with
  | zero => simp [icbrtAux]
  | succ n ih =>
      by_cases h : (n + 1) * (n + 1) * (n + 1) ≤ x
      · simp [icbrtAux, h]
      · simpa [icbrtAux, h] using ih

private theorem icbrtAux_greatest (x : Nat) :
    ∀ n m, m ≤ n → m * m * m ≤ x → m ≤ icbrtAux x n := by
  intro n
  induction n with
  | zero =>
      intro m hmn hm
      have hm0 : m = 0 := by omega
      subst hm0
      simp [icbrtAux]
  | succ n ih =>
      intro m hmn hm
      by_cases h : (n + 1) * (n + 1) * (n + 1) ≤ x
      · simp [icbrtAux, h]
        exact hmn
      · have hm_le_n : m ≤ n := by
          by_cases hm_eq : m = n + 1
          · subst hm_eq
            exact False.elim (h hm)
          · omega
        have hm_le_aux : m ≤ icbrtAux x n := ih m hm_le_n hm
        simpa [icbrtAux, h] using hm_le_aux

/-- Lower half of the floor specification: `icbrt(x)^3 ≤ x`. -/
theorem icbrt_cube_le (x : Nat) :
    icbrt x * icbrt x * icbrt x ≤ x := by
  unfold icbrt
  exact icbrtAux_cube_le x x

/-- Upper half of the floor specification: `x < (icbrt(x)+1)^3`. -/
theorem icbrt_lt_succ_cube (x : Nat) :
    x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := by
  by_cases hlt : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1)
  · exact hlt
  · have hle : (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) ≤ x := Nat.le_of_not_lt hlt
    have hpos : 0 < icbrt x + 1 := by omega
    have hmx : icbrt x + 1 ≤ x := by
      have hleCube : icbrt x + 1 ≤ (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) :=
        le_cube_of_pos hpos
      exact Nat.le_trans hleCube hle
    have hmax : icbrt x + 1 ≤ icbrt x := by
      unfold icbrt
      exact icbrtAux_greatest x x (icbrt x + 1) hmx hle
    exact False.elim ((Nat.not_succ_le_self (icbrt x)) hmax)

/-- Uniqueness: any `r` satisfying the floor specification equals `icbrt(x)`. -/
theorem icbrt_eq_of_bounds (x r : Nat)
    (hlo : r * r * r ≤ x)
    (hhi : x < (r + 1) * (r + 1) * (r + 1)) :
    r = icbrt x := by
  have hrx : r ≤ x := by
    by_cases hr0 : r = 0
    · omega
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hrle : r ≤ r * r * r := le_cube_of_pos hrpos
      exact Nat.le_trans hrle hlo
  have h1 : r ≤ icbrt x := by
    unfold icbrt
    exact icbrtAux_greatest x x r hrx hlo
  have h2 : icbrt x ≤ r := by
    by_cases hic : icbrt x ≤ r
    · exact hic
    · have hr1_le : r + 1 ≤ icbrt x := Nat.succ_le_of_lt (Nat.lt_of_not_ge hic)
      have hmono : (r + 1) * (r + 1) * (r + 1) ≤ icbrt x * icbrt x * icbrt x :=
        cube_monotone hr1_le
      have hicbrt : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
      have : (r + 1) * (r + 1) * (r + 1) ≤ x := Nat.le_trans hmono hicbrt
      exact False.elim (Nat.not_le_of_lt hhi this)
  exact Nat.le_antisymm h1 h2

end Tamago.Proof.Utils.Cbrt.Model
