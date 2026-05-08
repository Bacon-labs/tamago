import Tamago.Utils.FixedPointMathLib

namespace Tamago.Spec.Utils.FixedPointMathLibSpec

open Verity
open Tamago.Utils.FixedPointMathLib

/-
FixedPointMathLib specs describe pure arithmetic helpers. Each spec states the
normal mathematical result, the edge-case behavior at uint256 boundaries, and
simple bounds that make the helper safe to compose with token accounting.
-/

/-
saturatingAdd(x, y)

Properties specified:
- If x + y fits in uint256, the exact sum is returned.
- If x + y overflows uint256, the result is maxUint256.
- The result is at least x.
- The result is at least y.

Security conclusions:
- Addition returns the exact sum when it fits.
- Overflow saturates at maxUint256 instead of wrapping.
- The result is monotonic with respect to both inputs.
-/
def fixedPointMathLib_saturatingAdd_returns_exact_sum_when_no_overflow
    (x y result : Uint256) : Prop :=
  x.val + y.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    result.val = x.val + y.val

def fixedPointMathLib_saturatingAdd_overflow_returns_max
    (x y result : Uint256) : Prop :=
  Verity.Stdlib.Math.MAX_UINT256 < x.val + y.val → result = maxUint256

def fixedPointMathLib_saturatingAdd_result_at_least_left_input
    (x _y result : Uint256) : Prop :=
  x.val ≤ result.val

def fixedPointMathLib_saturatingAdd_result_at_least_right_input
    (_x y result : Uint256) : Prop :=
  y.val ≤ result.val

/-
saturatingMul(x, y)

Properties specified:
- If x * y fits in uint256, the exact product is returned.
- If x * y overflows uint256, the result is maxUint256.
- Multiplication by zero returns zero.

Security conclusions:
- Multiplication returns the exact product when it fits.
- Overflow saturates at maxUint256 instead of wrapping.
- Zero inputs preserve the expected zero result.
-/
def fixedPointMathLib_saturatingMul_returns_exact_product_when_no_overflow
    (x y result : Uint256) : Prop :=
  x.val * y.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    result.val = x.val * y.val

def fixedPointMathLib_saturatingMul_overflow_returns_max
    (x y result : Uint256) : Prop :=
  Verity.Stdlib.Math.MAX_UINT256 < x.val * y.val → result = maxUint256

def fixedPointMathLib_saturatingMul_left_zero_returns_zero
    (x _y result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_saturatingMul_right_zero_returns_zero
    (_x y result : Uint256) : Prop :=
  y.val = 0 → result = 0

/-
saturatingSub(x, y)

Properties specified:
- If y is greater than or equal to x, the result is zero.
- Otherwise, adding y back to the result reconstructs x.
- The result never exceeds x.

Security conclusions:
- Subtraction floors at zero instead of underflowing.
- When subtraction does not floor, the result is the exact difference.
- The result never exceeds the minuend.
-/
def fixedPointMathLib_saturatingSub_subtrahend_at_least_input_returns_zero
    (x y result : Uint256) : Prop :=
  x.val ≤ y.val → result = 0

def fixedPointMathLib_saturatingSub_exact_when_input_at_least_subtrahend
    (x y result : Uint256) : Prop :=
  y.val ≤ x.val → result.val + y.val = x.val

def fixedPointMathLib_saturatingSub_result_at_most_input
    (x _y result : Uint256) : Prop :=
  result.val ≤ x.val

/-
dist(x, y)

Properties specified:
- The result is the absolute distance between x and y in either order.

Security conclusions:
- Distance is independent of argument order.
- The helper avoids unsigned underflow when comparing two values.
-/
def fixedPointMathLib_dist_spec (x y result : Uint256) : Prop :=
  (x.val ≤ y.val → result.val + x.val = y.val) ∧
  (y.val ≤ x.val → result.val + y.val = x.val)

/-
avg(x, y)

Properties specified:
- Twice the result is at most x + y.
- x + y is less than twice the next integer after the result.

Security conclusions:
- The helper returns the mathematical floor average of x and y.
- The result is characterized without depending on the overflow-avoiding
  implementation strategy.
-/
def fixedPointMathLib_avg_twice_result_le_sum (x y result : Uint256) : Prop :=
  2 * result.val ≤ x.val + y.val

def fixedPointMathLib_avg_sum_lt_twice_next_result (x y result : Uint256) : Prop :=
  x.val + y.val < 2 * (result.val + 1)

/-
sqrt(x)

Properties specified:
- The result squared is at most x.
- The next integer squared is greater than x.

Security conclusions:
- The helper returns the mathematical floor square root.
-/
def fixedPointMathLib_sqrt_square_le_input (x result : Uint256) : Prop :=
  result.val * result.val ≤ x.val

def fixedPointMathLib_sqrt_input_lt_next_square (x result : Uint256) : Prop :=
  x.val < (result.val + 1) * (result.val + 1)

/-
cbrt(x)

Properties specified:
- The result cubed is at most x.
- The next integer cubed is greater than x.

Security conclusions:
- The helper returns the mathematical floor cube root.
-/
def fixedPointMathLib_cbrt_cube_le_input (x result : Uint256) : Prop :=
  result.val * result.val * result.val ≤ x.val

def fixedPointMathLib_cbrt_input_lt_next_cube (x result : Uint256) : Prop :=
  x.val < (result.val + 1) * (result.val + 1) * (result.val + 1)

/-
log2/log10/log256, rounded down

Properties specified:
- Zero returns zero.
- For nonzero x, base^result is at most x.
- x is always less than base^(result + 1).

Security conclusions:
- Each helper returns the mathematical floor logarithm in its base.
-/
def fixedPointMathLib_log2_zero_returns_zero (x result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_log2_power_le_input (x result : Uint256) : Prop :=
  x.val ≠ 0 → 2 ^ result.val ≤ x.val

def fixedPointMathLib_log2_input_lt_next_power (x result : Uint256) : Prop :=
  x.val < 2 ^ (result.val + 1)

def fixedPointMathLib_log10_zero_returns_zero (x result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_log10_power_le_input (x result : Uint256) : Prop :=
  x.val ≠ 0 → 10 ^ result.val ≤ x.val

def fixedPointMathLib_log10_input_lt_next_power (x result : Uint256) : Prop :=
  x.val < 10 ^ (result.val + 1)

def fixedPointMathLib_log256_zero_returns_zero (x result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_log256_power_le_input (x result : Uint256) : Prop :=
  x.val ≠ 0 → 256 ^ result.val ≤ x.val

def fixedPointMathLib_log256_input_lt_next_power (x result : Uint256) : Prop :=
  x.val < 256 ^ (result.val + 1)

/-
log2Up/log10Up/log256Up, rounded up

Properties specified:
- Zero returns zero.
- x is at most base^result.
- For x > 1, base^(result - 1) is still smaller than x.

Security conclusions:
- Each helper returns the mathematical ceiling logarithm in its base.
-/
def fixedPointMathLib_log2Up_zero_returns_zero (x result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_log2Up_input_le_power (x result : Uint256) : Prop :=
  x.val ≤ 2 ^ result.val

def fixedPointMathLib_log2Up_prev_power_lt_input (x result : Uint256) : Prop :=
  1 < x.val → 2 ^ (result.val - 1) < x.val

def fixedPointMathLib_log10Up_zero_returns_zero (x result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_log10Up_input_le_power (x result : Uint256) : Prop :=
  x.val ≤ 10 ^ result.val

def fixedPointMathLib_log10Up_prev_power_lt_input (x result : Uint256) : Prop :=
  1 < x.val → 10 ^ (result.val - 1) < x.val

def fixedPointMathLib_log256Up_zero_returns_zero (x result : Uint256) : Prop :=
  x.val = 0 → result = 0

def fixedPointMathLib_log256Up_input_le_power (x result : Uint256) : Prop :=
  x.val ≤ 256 ^ result.val

def fixedPointMathLib_log256Up_prev_power_lt_input (x result : Uint256) : Prop :=
  1 < x.val → 256 ^ (result.val - 1) < x.val

/-
clamp(x, minValue, maxValue)

Properties specified:
- If the range is invalid, the result is maxValue.
- For a valid range, the result lies inside [minValue, maxValue].
- Values already inside the range are unchanged.
- Values below or above the range snap to the nearest bound.

Security conclusions:
- Valid ranges always produce in-range results.
- Inputs already in range are preserved exactly.
- Out-of-range inputs are snapped to the nearest configured bound.
- Invalid ranges resolve deterministically to maxValue.
-/
def fixedPointMathLib_clamp_invalid_range_returns_max
    (_x minValue maxValue result : Uint256) : Prop :=
  maxValue.val < minValue.val → result = maxValue

def fixedPointMathLib_clamp_valid_range_bounds
    (_x minValue maxValue result : Uint256) : Prop :=
  minValue.val ≤ maxValue.val →
    minValue.val ≤ result.val ∧ result.val ≤ maxValue.val

def fixedPointMathLib_clamp_preserves_in_range
    (x minValue maxValue result : Uint256) : Prop :=
  minValue.val ≤ x.val ∧ x.val ≤ maxValue.val → result = x

def fixedPointMathLib_clamp_below_min_returns_min
    (x minValue maxValue result : Uint256) : Prop :=
  x.val < minValue.val ∧ minValue.val ≤ maxValue.val → result = minValue

def fixedPointMathLib_clamp_above_max_returns_max
    (x _minValue maxValue result : Uint256) : Prop :=
  maxValue.val < x.val → result = maxValue

end Tamago.Spec.Utils.FixedPointMathLibSpec
