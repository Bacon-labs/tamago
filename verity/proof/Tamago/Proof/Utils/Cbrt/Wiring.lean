/-
  Wiring: connects the octave certificates and error chain to the
  concrete `innerCbrt` algorithm, establishing:
  - Lower bound: m ≤ innerCbrt x for any m with m³ ≤ x
  - Upper bound: innerCbrt x ≤ icbrt x + 1 via the finite certificate
  - Octave-to-certificate mapping
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Tamago.Proof.Utils.Cbrt.Model
import Tamago.Proof.Utils.Cbrt.FloorBound
import Tamago.Proof.Utils.Cbrt.Contraction
import Tamago.Proof.Utils.Cbrt.OctaveCert
import Tamago.Proof.Utils.Cbrt.ErrorChain

namespace Tamago.Proof.Utils.Cbrt.Wiring

open Tamago.Proof.Utils.Cbrt.Model
open Tamago.Proof.Utils.Cbrt.FloorBound
open Tamago.Proof.Utils.Cbrt.Contraction
open Tamago.Proof.Utils.Cbrt.OctaveCert
open Tamago.Proof.Utils.Cbrt.ErrorChain

-- ============================================================================
-- Small Range
-- ============================================================================

private theorem innerCbrt_upper_of_lt_256 (x : Nat) (hx : x < 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  interval_cases x <;> native_decide

-- ============================================================================
-- Lower Bound
-- ============================================================================

/-- innerCbrt gives a lower bound: for any m with m³ ≤ x, m ≤ innerCbrt(x). -/
theorem innerCbrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m * m ≤ x) : m ≤ innerCbrt x := by
  unfold innerCbrt
  have hs := cbrtSeed_pos x
  have h1 := cbrtStep_pos x _ hx hs
  have h2 := cbrtStep_pos x _ hx h1
  have h3 := cbrtStep_pos x _ hx h2
  have h4 := cbrtStep_pos x _ hx h3
  exact cbrt_step_floor_bound x _ m h4 hm

/-- Positivity of `innerCbrt` for positive `x`. -/
theorem innerCbrt_pos (x : Nat) (hx : 0 < x) : 0 < innerCbrt x := by
  have h1 : (1 : Nat) * 1 * 1 ≤ x := by omega
  have h := innerCbrt_lower x 1 hx h1
  omega

-- ============================================================================
-- Octave-to-Certificate Mapping
-- ============================================================================

private theorem log2_octave (x : Nat) (hx : x ≠ 0) :
    2 ^ Nat.log2 x ≤ x ∧ x < 2 ^ (Nat.log2 x + 1) := by
  constructor
  · simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hx
  · simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) x

/-- The seed depends only on log2(x), so it matches the certificate seed. -/
theorem cbrtSeed_eq_octaveSeed (i : Fin 248) (x : Nat)
    (hOct : 2 ^ (i.val + certOffset) ≤ x ∧ x < 2 ^ (i.val + certOffset + 1)) :
    cbrtSeed x = seedOf i := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos (i.val + certOffset)) hOct.1
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hlog : Nat.log2 x = i.val + certOffset := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_eq_iff (b := 2) (m := i.val + certOffset) (n := x)
      (Or.inr ⟨by decide, hx0⟩)).2 hOct
  unfold cbrtSeed
  simp [hlog]
  have hseed := seed_eq i
  simp [seedOf, cbrtSeedMultiplier] at hseed ⊢
  rw [hseed]

/-- m = icbrt(x) lies within [loOf i, hiOf i] for x in octave i. -/
theorem m_within_cert_interval
    (i : Fin 248) (x m : Nat)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hOct : 2 ^ (i.val + certOffset) ≤ x ∧ x < 2 ^ (i.val + certOffset + 1)) :
    loOf i ≤ m ∧ m ≤ hiOf i := by
  have hloSq : loOf i * loOf i * loOf i ≤ 2 ^ (i.val + certOffset) := lo_cube_le_pow2 i
  have hloSqX : loOf i * loOf i * loOf i ≤ x := Nat.le_trans hloSq hOct.1
  have hlo : loOf i ≤ m := by
    by_cases h : loOf i ≤ m
    · exact h
    · have hlt : m < loOf i := Nat.lt_of_not_ge h
      have hm1 : m + 1 ≤ loOf i := Nat.succ_le_of_lt hlt
      have hm1cube : (m + 1) * (m + 1) * (m + 1) ≤ loOf i * loOf i * loOf i :=
        cube_monotone hm1
      have hm1x : (m + 1) * (m + 1) * (m + 1) ≤ x := Nat.le_trans hm1cube hloSqX
      exact False.elim ((Nat.not_lt_of_ge hm1x) hmhi)
  have hhiSq : 2 ^ (i.val + certOffset + 1) ≤
      (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) :=
    pow2_succ_le_hi_succ_cube i
  have hXHi : x < (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) :=
    Nat.lt_of_lt_of_le hOct.2 hhiSq
  have hhi : m ≤ hiOf i := by
    by_cases h : m ≤ hiOf i
    · exact h
    · have hlt : hiOf i < m := Nat.lt_of_not_ge h
      have hhi1 : hiOf i + 1 ≤ m := Nat.succ_le_of_lt hlt
      have hhicube : (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) ≤ m * m * m :=
        cube_monotone hhi1
      have hXmm : x < m * m * m := Nat.lt_of_lt_of_le hXHi hhicube
      exact False.elim ((Nat.not_lt_of_ge hmlo) hXmm)
  exact ⟨hlo, hhi⟩

-- ============================================================================
-- Upper Bound
-- ============================================================================

/-- Certificate-backed upper bound for a single octave. -/
theorem innerCbrt_upper_of_octave
    (i : Fin 248) (x m : Nat)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hOct : 2 ^ (i.val + certOffset) ≤ x ∧ x < 2 ^ (i.val + certOffset + 1)) :
    innerCbrt x ≤ m + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hOct.1
  have hinterval := m_within_cert_interval i x m hmlo hmhi hOct
  have hm2 : 2 ≤ m := Nat.le_trans (lo_ge_two i) hinterval.1
  have hseed : cbrtSeed x = seedOf i := cbrtSeed_eq_octaveSeed i x hOct
  have hrun : run5From x (seedOf i) ≤ m + 1 :=
    run5_le_m_plus_one i x m hm2 hmlo hmhi hinterval.1 hinterval.2
  have hinnerEq : innerCbrt x = run5From x (cbrtSeed x) :=
    innerCbrt_eq_run5From_seed x
  calc innerCbrt x = run5From x (cbrtSeed x) := hinnerEq
    _ = run5From x (seedOf i) := by rw [hseed]
    _ ≤ m + 1 := hrun

/-- Universal upper bound on uint256 domain:
    for every x ∈ [1, 2^256-1], innerCbrt x ≤ icbrt x + 1. -/
theorem innerCbrt_upper_u256 (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  by_cases hx_small : x < 256
  · exact innerCbrt_upper_of_lt_256 x hx_small
  · have hx256_le : 256 ≤ x := Nat.le_of_not_lt hx_small
    have hx0 : x ≠ 0 := Nat.ne_of_gt hx
    let n := Nat.log2 x
    have hn_bounds : 8 ≤ n := by
      dsimp [n]
      have hoctave := log2_octave x hx0
      by_cases h8 : 8 ≤ Nat.log2 x
      · exact h8
      · have hlt : Nat.log2 x + 1 ≤ 8 := by omega
        have hup : x < 2 ^ (Nat.log2 x + 1) := hoctave.2
        have hpow : 2 ^ (Nat.log2 x + 1) ≤ 2 ^ 8 :=
          Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlt
        have : x < 256 := Nat.lt_of_lt_of_le hup (by simpa using hpow)
        omega
    have hn_lt : n < 256 := by
      dsimp [n]
      exact (Nat.log2_lt hx0).2 hx256
    have hcert : certOffset = 8 := rfl
    let idx : Fin 248 := ⟨n - certOffset, by omega⟩
    have hidx_plus : idx.val + certOffset = n := by dsimp [idx]; omega
    have hOct : 2 ^ (idx.val + certOffset) ≤ x ∧ x < 2 ^ (idx.val + certOffset + 1) := by
      rw [hidx_plus]
      exact log2_octave x hx0
    let m := icbrt x
    have hmlo : m * m * m ≤ x := icbrt_cube_le x
    have hmhi : x < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube x
    exact innerCbrt_upper_of_octave idx x m hmlo hmhi hOct

end Tamago.Proof.Utils.Cbrt.Wiring
