import Contracts.Common

namespace src

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract FixedPointMathLib where
  storage

  function view WAD () : Uint256 := do
    return 1000000000000000000

  function view mulDivDown (x : Uint256, y : Uint256, denominator : Uint256) : Uint256 := do
    let product := mul x y
    return div product denominator

  function view mulDivUp (x : Uint256, y : Uint256, denominator : Uint256) : Uint256 := do
    let product := mul x y
    let rounded := add product (sub denominator 1)
    return div rounded denominator

  function view mulWadDown (x : Uint256, y : Uint256) : Uint256 := do
    let product := mul x y
    return div product 1000000000000000000

  function view mulWadUp (x : Uint256, y : Uint256) : Uint256 := do
    let product := mul x y
    let rounded := add product (sub 1000000000000000000 1)
    return div rounded 1000000000000000000

  function view divWadDown (x : Uint256, y : Uint256) : Uint256 := do
    let product := mul x 1000000000000000000
    return div product y

  function view divWadUp (x : Uint256, y : Uint256) : Uint256 := do
    let product := mul x 1000000000000000000
    let rounded := add product (sub y 1)
    return div rounded y

  function view ceilDiv (x : Uint256, y : Uint256) : Uint256 := do
    if x == 0 then
      return 0
    else
      let decremented := sub x 1
      let quotient := div decremented y
      return add quotient 1

end src
