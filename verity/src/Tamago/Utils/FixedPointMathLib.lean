import Contracts.Common

namespace Tamago.Utils

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256

/-
@title FixedPointMathLib
@notice Stateless unsigned integer math helpers for fixed-point-oriented
contracts and tests.
@dev Provides saturating arithmetic, distance, average, square and cube roots,
binary, decimal, and byte logarithms, and clamping.
-/
verity_contract FixedPointMathLibBase where
  storage

  constants
    maxUint256 : Uint256 := (sub 0 1)
    clzDeBruijnMagic : Uint256 := 0x8421084210842108cc6318c6db6d54be
    clzDeBruijnTable : Uint256 :=
      0xf8f9f9faf9fdfafbf9fdfcfdfafbfcfef9fafdfafcfcfbfefafafcfbffffffff

  /-
  @notice Adds two unsigned integers and saturates on overflow.
  @param x First addend.
  @param y Second addend.
  @return Sum, or max uint256 if the addition would overflow.
  -/
  function view saturatingAdd (x : Uint256, y : Uint256) : Uint256 := do
    let room := sub maxUint256 x
    if y > room then
      return maxUint256
    else
      return (add x y)

  /-
  @notice Multiplies two unsigned integers and saturates on overflow.
  @param x First factor.
  @param y Second factor.
  @return Product, or max uint256 if the multiplication would overflow.
  -/
  function view saturatingMul (x : Uint256, y : Uint256) : Uint256 := do
    let limit := div maxUint256 x
    if (x != 0) && (y > limit) then
      return maxUint256
    else
      return (mul x y)

  /-
  @notice Subtracts and saturates at zero on underflow.
  @param x Minuend.
  @param y Subtrahend.
  @return Difference, or zero if `y` is greater than `x`.
  -/
  function view saturatingSub (x : Uint256, y : Uint256) : Uint256 := do
    if y > x then
      return 0
    else
      return (sub x y)

  /-
  @notice Computes the absolute distance between two unsigned integers.
  @param x First value.
  @param y Second value.
  @return Absolute difference between `x` and `y`.
  -/
  function view dist (x : Uint256, y : Uint256) : Uint256 := do
    if x >= y then
      return (sub x y)
    else
      return (sub y x)

  /-
  @notice Computes the average of two unsigned integers without overflow.
  @param x First value.
  @param y Second value.
  @return Floor average of `x` and `y`.
  -/
  function view avg (x : Uint256, y : Uint256) : Uint256 := do
    if x >= y then
      return (add y (div (sub x y) 2))
    else
      return (add x (div (sub y x) 2))

  /-
  @notice Counts leading zero bits in a uint256 word.
  @param x Input value.
  @return Number of zero bits before the most significant set bit, or 256 for zero.
  -/
  function view clz (x : Uint256) : Uint256 := do
    let mut r := shl 7 (boolToWord (0xffffffffffffffffffffffffffffffff < x))
    r := bitOr r (shl 6 (boolToWord (0xffffffffffffffff < shr r x)))
    r := bitOr r (shl 5 (boolToWord (0xffffffff < shr r x)))
    r := bitOr r (shl 4 (boolToWord (0xffff < shr r x)))
    r := bitOr r (shl 3 (boolToWord (0xff < shr r x)))
    let y := shr r x
    let deBruijnIndex := bitAnd 0x1f (shr y clzDeBruijnMagic)
    let clzByte := byte deBruijnIndex clzDeBruijnTable
    return (add (bitXor r clzByte) (boolToWord (x == 0)))

  /-
  @notice Computes the integer square root.
  @param x Input value.
  @return Floor square root of `x`.
  -/
  function view sqrt (x : Uint256) : Uint256 := do
    /-
    Initial guess z = 2^⌊(n+1)/2⌋ where n = ⌊log₂(x)⌋. This seed gives ε₁ =
    0.0607 after one Babylonian step for all inputs. With ε_{n+1} ≈ ε²/2, 6
    steps yield 2⁻¹⁶⁰ relative error (>128 correct bits). We implicitly
    represent z₀ as log₂(z) so that the first `div` becomes a `shr`.
    -/
    let xClz ← clz x
    let mut z := shr 1 (sub 256 xClz)
    z := shr 1 (add (shl z 1) (shr z x))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    /-
    If `x+1` is a perfect square, the Babylonian method oscillates between ⌊√x⌋
    and ⌈√x⌉. Floor it. See:
    https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division
    -/
    return (sub z (boolToWord (div x z < z)))

  /-
  @notice Computes the integer cube root.
  @param x Input value.
  @return Floor cube root of `x`.
  -/
  function view cbrt (x : Uint256) : Uint256 := do
    /-
    Initial guess z ≈ c · 2𐞥 where b = ⌊log₂(x)⌋, q = ⌊b / 3⌋. The 8-bit
    fixed-point multipliers `c`: 149/128, 177/128, and 233/128 are selected by
    `b % 3` to balance each octave's worst-case final error. This gives >88 bits
    of precision after only 5 Newton-Raphson iterations. The `bitOr 1 ...` keeps
    z ≥ 1 when the shifted estimate is 0.
    -/
    let xClz ← clz x
    let b := sub 255 xClz
    let mut z := bitOr 1 (shr 7 (shl (div b 3) (add 121 (shl (mod b 3) 28))))
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    -- Round down.
    return (sub z (boolToWord (div x (mul z z) < z)))

  /-
  @notice Computes the base-256 logarithm.
  @param x Input value.
  @return Floor log base 256 of `x`.
  -/
  function view log256 (x : Uint256) : Uint256 := do
    let mut r := 0
    let mut value := x
    if 0xffffffffffffffffffffffffffffffff < value then
      value := shr 128 value
      r := 16
    else
      pure ()
    if 0xffffffffffffffff < value then
      value := shr 64 value
      r := add r 8
    else
      pure ()
    if 0xffffffff < value then
      value := shr 32 value
      r := add r 4
    else
      pure ()
    if 0xffff < value then
      value := shr 16 value
      r := add r 2
    else
      pure ()
    if 0xff < value then
      return (add r 1)
    else
      return r

  /-
  @notice Computes the base-256 logarithm rounded up.
  @param x Input value.
  @return Ceiling log base 256 of `x`.
  -/
  function view log256Up (x : Uint256) : Uint256 := do
    let mut r := 0
    let mut value := x
    if 0xffffffffffffffffffffffffffffffff < value then
      value := shr 128 value
      r := 16
    else
      pure ()
    if 0xffffffffffffffff < value then
      value := shr 64 value
      r := add r 8
    else
      pure ()
    if 0xffffffff < value then
      value := shr 32 value
      r := add r 4
    else
      pure ()
    if 0xffff < value then
      value := shr 16 value
      r := add r 2
    else
      pure ()
    if 0xff < value then
      r := add r 1
    else
      pure ()
    if shl (shl 3 r) 1 < x then
      return (add r 1)
    else
      return r

  /-
  @notice Computes the binary logarithm.
  @param x Input value.
  @return Floor log base 2 of `x`.
  -/
  function view log2 (x : Uint256) : Uint256 := do
    let mut r := 0
    let mut value := x
    if 0xffffffffffffffffffffffffffffffff < value then
      value := shr 128 value
      r := 128
    else
      pure ()
    if 0xffffffffffffffff < value then
      value := shr 64 value
      r := add r 64
    else
      pure ()
    if 0xffffffff < value then
      value := shr 32 value
      r := add r 32
    else
      pure ()
    if 0xffff < value then
      value := shr 16 value
      r := add r 16
    else
      pure ()
    if 0xff < value then
      value := shr 8 value
      r := add r 8
    else
      pure ()
    if 0xf < value then
      value := shr 4 value
      r := add r 4
    else
      pure ()
    if 0x3 < value then
      value := shr 2 value
      r := add r 2
    else
      pure ()
    if 0x1 < value then
      return (add r 1)
    else
      return r

  /-
  @notice Computes the binary logarithm rounded up.
  @param x Input value.
  @return Ceiling log base 2 of `x`.
  -/
  function view log2Up (x : Uint256) : Uint256 := do
    let mut r := 0
    let mut value := x
    if 0xffffffffffffffffffffffffffffffff < value then
      value := shr 128 value
      r := 128
    else
      pure ()
    if 0xffffffffffffffff < value then
      value := shr 64 value
      r := add r 64
    else
      pure ()
    if 0xffffffff < value then
      value := shr 32 value
      r := add r 32
    else
      pure ()
    if 0xffff < value then
      value := shr 16 value
      r := add r 16
    else
      pure ()
    if 0xff < value then
      value := shr 8 value
      r := add r 8
    else
      pure ()
    if 0xf < value then
      value := shr 4 value
      r := add r 4
    else
      pure ()
    if 0x3 < value then
      value := shr 2 value
      r := add r 2
    else
      pure ()
    if 0x1 < value then
      r := add r 1
    else
      pure ()
    if shl r 1 < x then
      return (add r 1)
    else
      return r

  /-
  @notice Computes the decimal logarithm.
  @param x Input value.
  @return Floor log base 10 of `x`.
  -/
  function view log10 (x : Uint256) : Uint256 := do
    let mut r := 0
    let mut value := x
    if 99999999999999999999999999999999999999 < value then
      value := div value 100000000000000000000000000000000000000
      r := 38
    else
      pure ()
    if 99999999999999999999 < value then
      value := div value 100000000000000000000
      r := add r 20
    else
      pure ()
    if 9999999999 < value then
      value := div value 10000000000
      r := add r 10
    else
      pure ()
    if 99999 < value then
      value := div value 100000
      r := add r 5
    else
      pure ()
    if 9 < value then
      r := add r 1
    else
      pure ()
    if 99 < value then
      r := add r 1
    else
      pure ()
    if 999 < value then
      r := add r 1
    else
      pure ()
    if 9999 < value then
      return (add r 1)
    else
      return r

  /-
  @notice Computes the decimal logarithm rounded up.
  @param x Input value.
  @return Ceiling log base 10 of `x`.
  -/
  function log10Up (x : Uint256) : Uint256 := do
    let r ← log10 x
    let mut scale := 1
    let mut exponent := r
    if 37 < exponent then
      scale := mul scale 100000000000000000000000000000000000000
      exponent := sub exponent 38
    else
      pure ()
    if 19 < exponent then
      scale := mul scale 100000000000000000000
      exponent := sub exponent 20
    else
      pure ()
    if 9 < exponent then
      scale := mul scale 10000000000
      exponent := sub exponent 10
    else
      pure ()
    if 4 < exponent then
      scale := mul scale 100000
      exponent := sub exponent 5
    else
      pure ()
    if 3 < exponent then
      scale := mul scale 10000
      exponent := sub exponent 4
    else
      pure ()
    if 1 < exponent then
      scale := mul scale 100
      exponent := sub exponent 2
    else
      pure ()
    if 0 < exponent then
      scale := mul scale 10
    else
      pure ()
    if scale < x then
      return (add r 1)
    else
      return r

  /-
  @notice Clamps a value between lower and upper bounds.
  @param x Value to clamp.
  @param minValue Lower bound.
  @param maxValue Upper bound.
  @return `x` bounded to the inclusive range [`minValue`, `maxValue`].
  -/
  function view clamp (x : Uint256, minValue : Uint256, maxValue : Uint256) : Uint256 := do
    let boundedBelow := max x minValue
    return (min boundedBelow maxValue)

namespace FixedPointMathLib

abbrev maxUint256 := FixedPointMathLibBase.maxUint256

abbrev saturatingAdd := FixedPointMathLibBase.saturatingAdd
abbrev saturatingMul := FixedPointMathLibBase.saturatingMul
abbrev saturatingSub := FixedPointMathLibBase.saturatingSub
abbrev dist := FixedPointMathLibBase.dist
abbrev avg := FixedPointMathLibBase.avg
abbrev clz := FixedPointMathLibBase.clz
abbrev sqrt := FixedPointMathLibBase.sqrt
abbrev cbrt := FixedPointMathLibBase.cbrt
abbrev log2 := FixedPointMathLibBase.log2
abbrev log2Up := FixedPointMathLibBase.log2Up
abbrev log10 := FixedPointMathLibBase.log10
abbrev log10Up := FixedPointMathLibBase.log10Up
abbrev log256 := FixedPointMathLibBase.log256
abbrev log256Up := FixedPointMathLibBase.log256Up
abbrev clamp := FixedPointMathLibBase.clamp

def spec : Compiler.CompilationModel.CompilationModel :=
  { FixedPointMathLibBase.spec with
    name := "FixedPointMathLib" }

end FixedPointMathLib

end Tamago.Utils
