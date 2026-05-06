import src.FixedPointMathLib

namespace spec.FixedPointMathLibSpec

open Verity
open Verity.EVM.Uint256

def fixed_WAD_spec (result : Uint256) : Prop :=
  result.val = 1000000000000000000

def fixed_mulDivDown_spec (x y denominator result : Uint256) : Prop :=
  result.val =
    if denominator.val = 0 then
      0
    else
      ((x.val * y.val) % Verity.Core.Uint256.modulus) / denominator.val

def fixed_mulDivUp_spec (x y denominator result : Uint256) : Prop :=
  result.val =
    if denominator.val = 0 then
      0
    else
      ((((x.val * y.val) % Verity.Core.Uint256.modulus) + (denominator.val - 1)) %
        Verity.Core.Uint256.modulus) / denominator.val

def fixed_mulWadDown_spec (x y result : Uint256) : Prop :=
  result.val =
    ((x.val * y.val) % Verity.Core.Uint256.modulus) / 1000000000000000000

def fixed_mulWadUp_spec (x y result : Uint256) : Prop :=
  result.val =
    ((((x.val * y.val) % Verity.Core.Uint256.modulus) + (1000000000000000000 - 1)) %
      Verity.Core.Uint256.modulus) / 1000000000000000000

def fixed_divWadDown_spec (x y result : Uint256) : Prop :=
  result.val =
    if y.val = 0 then
      0
    else
      ((x.val * 1000000000000000000) % Verity.Core.Uint256.modulus) / y.val

def fixed_divWadUp_spec (x y result : Uint256) : Prop :=
  result.val =
    if y.val = 0 then
      0
    else
      ((((x.val * 1000000000000000000) % Verity.Core.Uint256.modulus) + (y.val - 1)) %
        Verity.Core.Uint256.modulus) / y.val

def fixed_ceilDiv_spec (x y result : Uint256) : Prop :=
  result.val =
    if x.val = 0 then
      0
    else if y.val = 0 then
      1
    else
      ((x.val - 1) / y.val) + 1

end spec.FixedPointMathLibSpec
