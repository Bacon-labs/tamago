import spec.FixedPointMathLibSpec

namespace proof.FixedPointMathLibProof

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open Verity
open Verity.EVM.Uint256
open spec.FixedPointMathLibSpec

-- tama: discharges=fixed_WAD_spec
theorem WAD_returns_scale (s : ContractState) :
  fixed_WAD_spec ((src.FixedPointMathLib.WAD).run s).fst := by
  simp [fixed_WAD_spec, src.FixedPointMathLib.WAD, Bind.bind, Pure.pure]

-- tama: discharges=fixed_mulDivDown_spec
theorem mulDivDown_matches_formula (x y denominator : Uint256) (s : ContractState) :
  fixed_mulDivDown_spec x y denominator
    ((src.FixedPointMathLib.mulDivDown x y denominator).run s).fst := by
  simp [fixed_mulDivDown_spec, src.FixedPointMathLib.mulDivDown, Bind.bind, Pure.pure]

-- tama: discharges=fixed_mulDivUp_spec
theorem mulDivUp_matches_formula (x y denominator : Uint256) (s : ContractState) :
  fixed_mulDivUp_spec x y denominator
    ((src.FixedPointMathLib.mulDivUp x y denominator).run s).fst := by
  simp [fixed_mulDivUp_spec, src.FixedPointMathLib.mulDivUp, Bind.bind, Pure.pure]

-- tama: discharges=fixed_mulWadDown_spec
theorem mulWadDown_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_mulWadDown_spec x y ((src.FixedPointMathLib.mulWadDown x y).run s).fst := by
  simp [fixed_mulWadDown_spec, src.FixedPointMathLib.mulWadDown, Bind.bind, Pure.pure]

-- tama: discharges=fixed_mulWadUp_spec
theorem mulWadUp_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_mulWadUp_spec x y ((src.FixedPointMathLib.mulWadUp x y).run s).fst := by
  simp [fixed_mulWadUp_spec, src.FixedPointMathLib.mulWadUp, Bind.bind, Pure.pure]

-- tama: discharges=fixed_divWadDown_spec
theorem divWadDown_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_divWadDown_spec x y ((src.FixedPointMathLib.divWadDown x y).run s).fst := by
  simp [fixed_divWadDown_spec, src.FixedPointMathLib.divWadDown, Bind.bind, Pure.pure]

-- tama: discharges=fixed_divWadUp_spec
theorem divWadUp_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_divWadUp_spec x y ((src.FixedPointMathLib.divWadUp x y).run s).fst := by
  simp [fixed_divWadUp_spec, src.FixedPointMathLib.divWadUp, Bind.bind, Pure.pure]

-- tama: discharges=fixed_ceilDiv_spec
theorem ceilDiv_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_ceilDiv_spec x y ((src.FixedPointMathLib.ceilDiv x y).run s).fst := by
  by_cases h_zero : x = 0
  · subst h_zero
    simp [fixed_ceilDiv_spec, src.FixedPointMathLib.ceilDiv, Contract.run, ContractResult.fst,
      Bind.bind, Pure.pure, Verity.bind, Verity.pure]
  · have h_not_zero : (x == 0) = false := by
      simpa [beq_iff_eq, h_zero]
    simp [fixed_ceilDiv_spec, src.FixedPointMathLib.ceilDiv, Contract.run, ContractResult.fst,
      Bind.bind, Pure.pure, Verity.bind, Verity.pure, h_not_zero]

end proof.FixedPointMathLibProof
