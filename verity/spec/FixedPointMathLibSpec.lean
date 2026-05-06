import src.FixedPointMathLib

namespace spec.FixedPointMathLibSpec

open Verity
open Verity.EVM.Uint256

def fixed_WAD_spec (result : Uint256) : Prop :=
  result = 1000000000000000000

def fixed_mulDivDown_spec (x y denominator result : Uint256) : Prop :=
  result = div (mul x y) denominator

def fixed_mulDivUp_spec (x y denominator result : Uint256) : Prop :=
  result = div (add (mul x y) (sub denominator 1)) denominator

def fixed_mulWadDown_spec (x y result : Uint256) : Prop :=
  result = div (mul x y) 1000000000000000000

def fixed_mulWadUp_spec (x y result : Uint256) : Prop :=
  result = div (add (mul x y) (sub 1000000000000000000 1)) 1000000000000000000

def fixed_divWadDown_spec (x y result : Uint256) : Prop :=
  result = div (mul x 1000000000000000000) y

def fixed_divWadUp_spec (x y result : Uint256) : Prop :=
  result = div (add (mul x 1000000000000000000) (sub y 1)) y

def fixed_ceilDiv_spec (x y result : Uint256) : Prop :=
  result = if x == 0 then 0 else add (div (sub x 1) y) 1

end spec.FixedPointMathLibSpec
