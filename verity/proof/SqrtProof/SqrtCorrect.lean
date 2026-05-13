/-
  Arithmetic correctness components for the optimized square-root algorithm.

  Theorem 1 (innerSqrt_correct):
    Lower-bound component: if m² ≤ x then m ≤ innerSqrt(x) (for x > 0).

  Theorem 2 (floorSqrt_correct):
    Given a 1-ULP bracket for innerSqrt(x), floorSqrt(x) satisfies
    r² ≤ x < (r+1)².
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import SqrtProof.FloorBound
import SqrtProof.StepMono
import SqrtProof.CertifiedChain

-- ============================================================================
-- Part 1: Arithmetic model
-- ============================================================================

/-- The seed: z₀ = 2^⌊(log2(x)+1)/2⌋. For x=0, returns 0.
    Matches EVM: shl(shr(1, sub(256, clz(x))), 1)
    Since 256 - clz(x) = bitLength(x) = log2(x) + 1 for x > 0. -/
def sqrtSeed (x : Nat) : Nat :=
  if x = 0 then 0
  else 1 <<< ((Nat.log2 x + 1) / 2)

/-- _sqrt: seed + 6 Babylonian steps. Returns z ∈ {isqrt(x), isqrt(x)+1}. -/
def innerSqrt (x : Nat) : Nat :=
  if x = 0 then 0
  else
    let z := sqrtSeed x
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    let z := bstep x z
    z

/-- sqrt: _sqrt with floor correction. Returns exactly isqrt(x).
    Matches: z := sub(z, lt(div(x, z), z)) -/
def floorSqrt (x : Nat) : Nat :=
  let z := innerSqrt x
  z - if x / z < z then 1 else 0

-- ============================================================================
-- Part 2: Lower bound (composing Lemma 1)
-- ============================================================================

/-- The seed is positive for x > 0. -/
theorem sqrtSeed_pos (x : Nat) (hx : 0 < x) :
    0 < sqrtSeed x := by
  unfold sqrtSeed
  simp [Nat.ne_of_gt hx]
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.lt_of_lt_of_le (by omega : 0 < 1) (Nat.one_le_pow _ 2 (by omega))

/-- bstep preserves positivity when x > 0 and z > 0. -/
theorem bstep_pos (x z : Nat) (hx : 0 < x) (hz : 0 < z) : 0 < bstep x z := by
  unfold bstep
  -- For x ≥ 1 and z ≥ 1: z + x/z ≥ 2 (since z ≥ 1 and x/z ≥ 1 when z = 1,
  -- or z ≥ 2 when x/z = 0). So (z + x/z)/2 ≥ 1.
  by_cases hle : x < z
  · -- x < z, so x/z = 0. But z ≥ 2 (since x ≥ 1 and x < z means z ≥ 2).
    have : x / z = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hle)
    omega
  · -- x ≥ z, so x/z ≥ 1
    have : 0 < x / z := Nat.div_pos (by omega) hz
    omega

-- ============================================================================
-- Part 4: Main theorems
-- ============================================================================

/-- innerSqrt gives a lower bound: for any m with m² ≤ x, m ≤ innerSqrt(x).
    This follows from 6 applications of babylon_step_floor_bound. -/
theorem innerSqrt_lower (x m : Nat) (hx : 0 < x)
    (hm : m * m ≤ x) : m ≤ innerSqrt x := by
  unfold innerSqrt
  simp [Nat.ne_of_gt hx]
  -- The seed is positive
  have hs := sqrtSeed_pos x hx
  -- Each bstep preserves positivity (x > 0)
  -- Chain: m ≤ bstep x (bstep x (... (bstep x (sqrtSeed x))))
  -- Each step: if m² ≤ x and z > 0, then m ≤ bstep x z
  -- bstep is defined in FloorBound
  -- babylon_step_floor_bound : m*m ≤ x → 0 < z → m ≤ (z + x/z)/2
  have h1 := bstep_pos x _ hx hs
  have h2 := bstep_pos x _ hx h1
  have h3 := bstep_pos x _ hx h2
  have h4 := bstep_pos x _ hx h3
  have h5 := bstep_pos x _ hx h4
  -- Apply floor bound at the last step (z₅ is positive by h5)
  exact babylon_step_floor_bound x _ m h5 hm

/-- Unfolding identity: `innerSqrt` is six steps starting from `sqrtSeed`. -/
theorem innerSqrt_eq_run6From (x : Nat) (hx : 0 < x) :
    innerSqrt x = SqrtCertified.run6From x (sqrtSeed x) := by
  unfold innerSqrt SqrtCertified.run6From
  simp [Nat.ne_of_gt hx, bstep]

/-- Finite-certificate upper bound: if `m` is bracketed by the octave certificate,
    then six steps from the actual seed satisfy `innerSqrt x ≤ m + 1`. -/
theorem innerSqrt_upper_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = SqrtCert.seedOf i)
    (hlo : SqrtCert.loOf i ≤ m)
    (hhi : m ≤ SqrtCert.hiOf i) :
    innerSqrt x ≤ m + 1 := by
  have hrun : SqrtCertified.run6From x (SqrtCert.seedOf i) ≤ m + 1 :=
    SqrtCertified.run6_le_m_plus_one i x m hm hmlo hmhi hlo hhi
  calc
    innerSqrt x = SqrtCertified.run6From x (sqrtSeed x) := innerSqrt_eq_run6From x hx
    _ = SqrtCertified.run6From x (SqrtCert.seedOf i) := by simp [hseed]
    _ ≤ m + 1 := hrun

/-- Certificate-backed 1-ULP bracket for `innerSqrt`. -/
theorem innerSqrt_bracket_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = SqrtCert.seedOf i)
    (hlo : SqrtCert.loOf i ≤ m)
    (hhi : m ≤ SqrtCert.hiOf i) :
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  exact ⟨innerSqrt_lower x m hx hmlo, innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hlo hhi⟩

/-- `sqrtSeed` agrees with the finite-certificate seed on octave `i`. -/
theorem sqrtSeed_eq_seedOf_of_octave
    (i : Fin 256) (x : Nat)
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    sqrtSeed x = SqrtCert.seedOf i := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hlog : Nat.log2 x = i.val := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_eq_iff (b := 2) (m := i.val) (n := x)
      (Or.inr ⟨by decide, hx0⟩)).2 hOct
  unfold sqrtSeed SqrtCert.seedOf
  simp [Nat.ne_of_gt hx, hlog]

/-- From the certified octave endpoints and `m² ≤ x < (m+1)²`,
    derive `m ∈ [loOf i, hiOf i]`. -/
theorem m_within_cert_interval
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i := by
  have hloSq : SqrtCert.loOf i * SqrtCert.loOf i ≤ 2 ^ i.val := SqrtCert.lo_sq_le_pow2 i
  have hloSqX : SqrtCert.loOf i * SqrtCert.loOf i ≤ x := Nat.le_trans hloSq hOct.1
  have hlo : SqrtCert.loOf i ≤ m := by
    by_cases h : SqrtCert.loOf i ≤ m
    · exact h
    · have hlt : m < SqrtCert.loOf i := Nat.lt_of_not_ge h
      have hm1 : m + 1 ≤ SqrtCert.loOf i := Nat.succ_le_of_lt hlt
      have hm1sq : (m + 1) * (m + 1) ≤ SqrtCert.loOf i * SqrtCert.loOf i :=
        Nat.mul_le_mul hm1 hm1
      have hm1x : (m + 1) * (m + 1) ≤ x := Nat.le_trans hm1sq hloSqX
      exact False.elim ((Nat.not_lt_of_ge hm1x) hmhi)
  have hhiSq : 2 ^ (i.val + 1) ≤ (SqrtCert.hiOf i + 1) * (SqrtCert.hiOf i + 1) :=
    SqrtCert.pow2_succ_le_hi_succ_sq i
  have hXHi : x < (SqrtCert.hiOf i + 1) * (SqrtCert.hiOf i + 1) :=
    Nat.lt_of_lt_of_le hOct.2 hhiSq
  have hhi : m ≤ SqrtCert.hiOf i := by
    by_cases h : m ≤ SqrtCert.hiOf i
    · exact h
    · have hlt : SqrtCert.hiOf i < m := Nat.lt_of_not_ge h
      have hhi1 : SqrtCert.hiOf i + 1 ≤ m := Nat.succ_le_of_lt hlt
      have hhimsq : (SqrtCert.hiOf i + 1) * (SqrtCert.hiOf i + 1) ≤ m * m :=
        Nat.mul_le_mul hhi1 hhi1
      have hXmm : x < m * m := Nat.lt_of_lt_of_le hXHi hhimsq
      exact False.elim ((Nat.not_lt_of_ge hmlo) hXmm)
  exact ⟨hlo, hhi⟩

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
  have hseed : sqrtSeed x = SqrtCert.seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
  have hinterval : SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i :=
    m_within_cert_interval i x m hmlo hmhi hOct
  exact innerSqrt_upper_cert i x m hx hm hmlo hmhi hseed hinterval.1 hinterval.2

/-- Certificate-backed 1-ULP bracket under octave membership. -/
theorem innerSqrt_bracket_of_octave
    (i : Fin 256) (x m : Nat)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hOct : 2 ^ i.val ≤ x ∧ x < 2 ^ (i.val + 1)) :
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos i.val) hOct.1
  exact ⟨innerSqrt_lower x m hx hmlo, innerSqrt_upper_of_octave i x m hmlo hmhi hOct⟩

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
  · -- x/z < z means z² > x (since z * (x/z) ≤ x < z * z)
    simp [h_lt]
    have h_zsq : x < z * z := by
      have h_euc := Nat.div_add_mod x z
      have h_mod := Nat.mod_lt x hz
      -- x < z * (x/z + 1) and x/z + 1 ≤ z, so x < z * z
      have h1 : x < z * (x / z + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left z (by omega))
    constructor
    · exact hlo
    · have : z - 1 + 1 = z := by omega
      rw [this]; exact h_zsq
  · -- x/z ≥ z means z² ≤ x
    simp [h_lt]
    simp only [Nat.not_lt] at h_lt
    have h_zsq : z * z ≤ x := by
      calc z * z ≤ z * (x / z) := Nat.mul_le_mul_left z h_lt
        _ ≤ x := Nat.mul_div_le x z
    exact ⟨h_zsq, hhi⟩

-- ============================================================================
-- Named wrappers for the advertised theorem entry points
-- ============================================================================

/-- `innerSqrt_correct`: established lower-bound component.
    For any witness `m` with `m² ≤ x` and `x > 0`, `innerSqrt x` is at least `m`. -/
theorem innerSqrt_correct (x m : Nat) (hx : 0 < x) (hm : m * m ≤ x) :
    m ≤ innerSqrt x :=
  innerSqrt_lower x m hx hm

/-- `floorSqrt_correct`: correction-step correctness under a 1-ULP bracket
    for the inner approximation. -/
theorem floorSqrt_correct (x : Nat) (hz : 0 < innerSqrt x)
    (hlo : (innerSqrt x - 1) * (innerSqrt x - 1) ≤ x)
    (hhi : x < (innerSqrt x + 1) * (innerSqrt x + 1)) :
    let r := floorSqrt x
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  unfold floorSqrt
  simpa [Nat.ne_of_gt hz] using floor_correction x (innerSqrt x) hz hlo hhi

/-- End-to-end correction theorem from the finite certificate assumptions. -/
theorem floorSqrt_correct_cert
    (i : Fin 256) (x m : Nat)
    (hx : 0 < x)
    (hm : 0 < m)
    (hmlo : m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1))
    (hseed : sqrtSeed x = SqrtCert.seedOf i)
    (hlo : SqrtCert.loOf i ≤ m)
    (hhi : m ≤ SqrtCert.hiOf i) :
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

/-- End-to-end correctness under octave membership plus the witness
    `m² ≤ x < (m+1)²` (so `m` is the integer square root witness). -/
theorem floorSqrt_correct_of_octave
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
  have hseed : sqrtSeed x = SqrtCert.seedOf i := sqrtSeed_eq_seedOf_of_octave i x hOct
  have hinterval : SqrtCert.loOf i ≤ m ∧ m ≤ SqrtCert.hiOf i :=
    m_within_cert_interval i x m hmlo hmhi hOct
  exact floorSqrt_correct_cert i x m hx hm hmlo hmhi hseed hinterval.1 hinterval.2

/-- Universal `innerSqrt` bracket on uint256 domain:
    choose `m = Nat.sqrt x` and derive `m ≤ innerSqrt x ≤ m+1`. -/
theorem innerSqrt_bracket_u256
    (x : Nat)
    (hx : 0 < x)
    (hx256 : x < 2 ^ 256) :
    let m := Nat.sqrt x
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
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
  exact innerSqrt_bracket_of_octave i x m hmlo hmhi hOct

/-- Universal `innerSqrt` bracket on uint256 domain (including `x = 0`). -/
theorem innerSqrt_bracket_u256_all
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let m := Nat.sqrt x
    m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerSqrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    simpa using innerSqrt_bracket_u256 x hx hx256

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

/-- Canonical witness package for the advertised uint256 statement. -/
theorem sqrt_witness_correct_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
  ∃ m, m * m ≤ x ∧ x < (m + 1) * (m + 1) ∧
      m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 := by
  refine ⟨Nat.sqrt x, Nat.sqrt_le x, Nat.lt_succ_sqrt x, ?_⟩
  simpa using innerSqrt_bracket_u256_all x hx256
