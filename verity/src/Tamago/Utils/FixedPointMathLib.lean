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

  function view saturatingAdd (x : Uint256, y : Uint256) : Uint256 := do
    let room := sub maxUint256 x
    if y > room then
      return maxUint256
    else
      return (add x y)

  function view saturatingMul (x : Uint256, y : Uint256) : Uint256 := do
    let limit := div maxUint256 x
    if (x != 0) && (y > limit) then
      return maxUint256
    else
      return (mul x y)

  function view saturatingSub (x : Uint256, y : Uint256) : Uint256 := do
    if y > x then
      return 0
    else
      return (sub x y)

  function view dist (x : Uint256, y : Uint256) : Uint256 := do
    if x >= y then
      return (sub x y)
    else
      return (sub y x)

  function view avg (x : Uint256, y : Uint256) : Uint256 := do
    if x >= y then
      return (add y (div (sub x y) 2))
    else
      return (add x (div (sub y x) 2))

  function view sqrt (x : Uint256) : Uint256 := do
    let mut z := 181
    let mut r := 0
    if 0xffffffffffffffffffffffffffffffffff < x then
      r := shl 7 1
    else
      pure ()
    if 0xffffffffffffffffff < shr r x then
      r := bitOr r (shl 6 1)
    else
      pure ()
    if 0xffffffffff < shr r x then
      r := bitOr r (shl 5 1)
    else
      pure ()
    if 0xffffff < shr r x then
      r := bitOr r (shl 4 1)
    else
      pure ()
    z := shl (shr 1 r) z
    z := shr 18 (mul z (add (shr r x) 65536))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    z := shr 1 (add z (div x z))
    if div x z < z then
      return (sub z 1)
    else
      return z

  function view cbrt (x : Uint256) : Uint256 := do
    let mut r := 0
    if 0xffffffffffffffffffffffffffffffff < x then
      r := shl 7 1
    else
      pure ()
    if 0xffffffffffffffff < shr r x then
      r := bitOr r (shl 6 1)
    else
      pure ()
    if 0xffffffff < shr r x then
      r := bitOr r (shl 5 1)
    else
      pure ()
    if 0xffff < shr r x then
      r := bitOr r (shl 4 1)
    else
      pure ()
    if 0xff < shr r x then
      r := bitOr r (shl 3 1)
    else
      pure ()

    let mut seedBase := 15
    if 0xf < shr r x then
      seedBase := 30
    else
      pure ()
    let mut z := div (shl (div r 3) seedBase) (bitXor 7 (mod r 3))
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    z := div (add (add (div x (mul z z)) z) z) 3
    if div x (mul z z) < z then
      return (sub z 1)
    else
      return z

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
