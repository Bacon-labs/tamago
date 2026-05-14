/-
  Nat model of the optimized square-root algorithm.

  Defines the Babylonian (Heron) step, seed, inner approximation (seed + 6 steps),
  and the floor-corrected result.
-/
import Init

namespace Sqrt.Model

-- ============================================================================
-- Definitions
-- ============================================================================

/-- One Babylonian step: ⌊(z + ⌊x/z⌋) / 2⌋. -/
def sqrtStep (x z : Nat) : Nat := (z + x / z) / 2

/-- The seed: z₀ = 2^⌊(log2(x)+1)/2⌋. For x=0, returns 0.
    Matches EVM: shl(shr(1, sub(256, clz(x))), 1) -/
def sqrtSeed (x : Nat) : Nat :=
  if x = 0 then 0
  else 1 <<< ((Nat.log2 x + 1) / 2)

/-- innerSqrt: seed + 6 Babylonian steps. Returns z ∈ {isqrt(x), isqrt(x)+1}. -/
def innerSqrt (x : Nat) : Nat :=
  if x = 0 then 0
  else
    let z := sqrtSeed x
    let z := sqrtStep x z
    let z := sqrtStep x z
    let z := sqrtStep x z
    let z := sqrtStep x z
    let z := sqrtStep x z
    let z := sqrtStep x z
    z

/-- floorSqrt: innerSqrt with floor correction. Returns exactly isqrt(x).
    Matches EVM: z := sub(z, lt(div(x, z), z)) -/
def floorSqrt (x : Nat) : Nat :=
  let z := innerSqrt x
  z - if x / z < z then 1 else 0

end Sqrt.Model
