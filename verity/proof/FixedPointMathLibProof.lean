import spec.FixedPointMathLibSpec

namespace proof.FixedPointMathLibProof

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open Verity
open Verity.EVM.Uint256
open spec.FixedPointMathLibSpec

private def WAD_NAT : Nat := 1000000000000000000

private def UINT256_MODULUS : Nat := Verity.Core.Uint256.modulus

private def word (n : Nat) : Nat :=
  n % UINT256_MODULUS

private def wordProduct (x y : Nat) : Nat :=
  word (x * y)

private def wordSum (x y : Nat) : Nat :=
  word (x + y)

private theorem div_val (a b : Uint256) :
    (div a b).val = if b.val = 0 then 0 else a.val / b.val := by
  by_cases h_zero : b.val = 0
  · simp [Verity.EVM.Uint256.div, Verity.Core.Uint256.div, h_zero]
  · have h_div_lt : a.val / b.val < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
    simp [Verity.EVM.Uint256.div, Verity.Core.Uint256.div, h_zero,
      Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt h_div_lt]

private theorem mul_val (a b : Uint256) :
    (mul a b).val = wordProduct a.val b.val := by
  simp [wordProduct, word, UINT256_MODULUS, Verity.EVM.Uint256.mul,
    Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]

private theorem add_val (a b : Uint256) :
    (add a b).val = wordSum a.val b.val := by
  simp [wordSum, word, UINT256_MODULUS, Verity.EVM.Uint256.add,
    Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]

private theorem sub_one_val_of_ne_zero (a : Uint256) (h : a.val ≠ 0) :
    (sub a 1).val = a.val - 1 := by
  have h_one_le : (1 : Uint256).val ≤ a.val := by
    simpa using Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
  simpa [HSub.hSub] using Verity.EVM.Uint256.sub_eq_of_le (a := a) (b := (1 : Uint256)) h_one_le

private theorem wad_nat_lt_modulus : WAD_NAT < Verity.Core.Uint256.modulus := by
  simp [WAD_NAT, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

private theorem wad_val :
    (1000000000000000000 : Uint256).val = WAD_NAT := by
  change (Verity.Core.Uint256.ofNat 1000000000000000000).val = WAD_NAT
  change 1000000000000000000 % Verity.Core.Uint256.modulus = WAD_NAT
  rw [WAD_NAT]
  exact Nat.mod_eq_of_lt wad_nat_lt_modulus

private theorem wad_ne_zero :
    (1000000000000000000 : Uint256).val ≠ 0 := by
  rw [wad_val]
  simp [WAD_NAT]

private theorem wad_nat_ne_zero : WAD_NAT ≠ 0 := by
  simp [WAD_NAT]

private theorem one_lt_uint256_modulus : (1 : Nat) < Verity.Core.Uint256.modulus := by
  simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

private theorem wordSum_zero_one : wordSum 0 1 = 1 := by
  simp [wordSum, word, UINT256_MODULUS, Nat.mod_eq_of_lt one_lt_uint256_modulus]

private theorem wordProduct_eq_mod (x y : Nat) :
    wordProduct x y = (x * y) % Verity.Core.Uint256.modulus := by
  simp [wordProduct, word, UINT256_MODULUS]

private theorem wordSum_wordProduct_eq_mod (x y z : Nat) :
    wordSum (wordProduct x y) z = (x * y + z) % Verity.Core.Uint256.modulus := by
  simp [wordSum, wordProduct, word, UINT256_MODULUS, Nat.add_mod]

private theorem sub_wad_one_val :
    (sub (1000000000000000000 : Uint256) 1).val = WAD_NAT - 1 := by
  simpa [wad_val] using sub_one_val_of_ne_zero (1000000000000000000 : Uint256) wad_ne_zero

private theorem ceil_add_val_of_pos (x y : Uint256) (hx : x.val ≠ 0) (hy : y.val ≠ 0) :
    (add (div (sub x 1) y) 1).val = (x.val - 1) / y.val + 1 := by
  have hx_pos : 0 < x.val := Nat.pos_of_ne_zero hx
  have h_sub_lt : x.val - 1 < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
  have h_div_lt : (x.val - 1) / y.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h_sub_lt
  have h_div_succ_lt : (x.val - 1) / y.val + 1 < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt
      (Nat.succ_le_of_lt
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hx_pos (by decide))))
      x.isLt
  have h_sub : (sub x 1).val = x.val - 1 := sub_one_val_of_ne_zero x hx
  have h_div : (div (sub x 1) y).val = (x.val - 1) / y.val := by
    rw [div_val]
    simp [hy, h_sub]
  calc
    (add (div (sub x 1) y) 1).val
        = wordSum (div (sub x 1) y).val (1 : Uint256).val := add_val _ _
    _ = (((x.val - 1) / y.val) + 1) % Verity.Core.Uint256.modulus := by
        simp [wordSum, word, UINT256_MODULUS, h_div]
    _ = (x.val - 1) / y.val + 1 := Nat.mod_eq_of_lt h_div_succ_lt

-- tama: discharges=fixed_WAD_spec
theorem WAD_returns_scale (s : ContractState) :
  fixed_WAD_spec ((src.FixedPointMathLib.WAD).run s).fst := by
  simp [fixed_WAD_spec, WAD_NAT, src.FixedPointMathLib.WAD, Bind.bind, Pure.pure, wad_val]

-- tama: discharges=fixed_mulDivDown_spec
theorem mulDivDown_matches_formula (x y denominator : Uint256) (s : ContractState) :
  fixed_mulDivDown_spec x y denominator
    ((src.FixedPointMathLib.mulDivDown x y denominator).run s).fst := by
  simp [fixed_mulDivDown_spec, src.FixedPointMathLib.mulDivDown, Bind.bind, Pure.pure,
    div_val, mul_val, wordProduct_eq_mod]

-- tama: discharges=fixed_mulDivUp_spec
theorem mulDivUp_matches_formula (x y denominator : Uint256) (s : ContractState) :
  fixed_mulDivUp_spec x y denominator
    ((src.FixedPointMathLib.mulDivUp x y denominator).run s).fst := by
  by_cases h_zero : denominator.val = 0
  · simp [fixed_mulDivUp_spec, src.FixedPointMathLib.mulDivUp, Bind.bind, Pure.pure,
      div_val, h_zero]
  · simp [fixed_mulDivUp_spec, src.FixedPointMathLib.mulDivUp, Bind.bind, Pure.pure,
      div_val, add_val, mul_val, sub_one_val_of_ne_zero denominator h_zero, h_zero,
      wordSum_wordProduct_eq_mod]

-- tama: discharges=fixed_mulWadDown_spec
theorem mulWadDown_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_mulWadDown_spec x y ((src.FixedPointMathLib.mulWadDown x y).run s).fst := by
  simp [fixed_mulWadDown_spec, src.FixedPointMathLib.mulWadDown, Bind.bind, Pure.pure,
    div_val, mul_val, wad_val, wad_ne_zero, wad_nat_ne_zero, WAD_NAT, wordProduct_eq_mod]

-- tama: discharges=fixed_mulWadUp_spec
theorem mulWadUp_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_mulWadUp_spec x y ((src.FixedPointMathLib.mulWadUp x y).run s).fst := by
  simp [fixed_mulWadUp_spec, src.FixedPointMathLib.mulWadUp, Bind.bind, Pure.pure,
    div_val, add_val, mul_val, wad_val, wad_ne_zero, wad_nat_ne_zero, sub_wad_one_val,
    WAD_NAT, wordSum_wordProduct_eq_mod]

-- tama: discharges=fixed_divWadDown_spec
theorem divWadDown_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_divWadDown_spec x y ((src.FixedPointMathLib.divWadDown x y).run s).fst := by
  simp [fixed_divWadDown_spec, src.FixedPointMathLib.divWadDown, Bind.bind, Pure.pure,
    div_val, mul_val, wad_val, WAD_NAT, wordProduct_eq_mod]

-- tama: discharges=fixed_divWadUp_spec
theorem divWadUp_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_divWadUp_spec x y ((src.FixedPointMathLib.divWadUp x y).run s).fst := by
  by_cases h_zero : y.val = 0
  · simp [fixed_divWadUp_spec, src.FixedPointMathLib.divWadUp, Bind.bind, Pure.pure,
      div_val, h_zero]
  · simp [fixed_divWadUp_spec, src.FixedPointMathLib.divWadUp, Bind.bind, Pure.pure,
      div_val, add_val, mul_val, wad_val, sub_one_val_of_ne_zero y h_zero, h_zero,
      WAD_NAT, wordSum_wordProduct_eq_mod]

-- tama: discharges=fixed_ceilDiv_spec
theorem ceilDiv_matches_formula (x y : Uint256) (s : ContractState) :
  fixed_ceilDiv_spec x y ((src.FixedPointMathLib.ceilDiv x y).run s).fst := by
  by_cases h_zero_val : x.val = 0
  · have h_zero : x = 0 := Verity.Core.Uint256.ext (by simpa using h_zero_val)
    subst h_zero
    simp [fixed_ceilDiv_spec, src.FixedPointMathLib.ceilDiv, Contract.run, ContractResult.fst,
      Bind.bind, Pure.pure, Verity.bind, Verity.pure]
  · have h_not_zero : (x == 0) = false := by
      simp [beq_iff_eq]
      intro h_eq
      exact h_zero_val (congrArg (fun value : Uint256 => value.val) h_eq)
    by_cases h_y_zero : y.val = 0
    · have h_div_zero : (div (sub x 1) y).val = 0 := by
        simp [div_val, h_y_zero]
      simp [fixed_ceilDiv_spec, src.FixedPointMathLib.ceilDiv, Contract.run, ContractResult.fst,
        Bind.bind, Pure.pure, Verity.bind, Verity.pure, h_not_zero, h_zero_val, h_y_zero,
        h_div_zero, add_val, wordSum_zero_one]
    · simp [fixed_ceilDiv_spec, src.FixedPointMathLib.ceilDiv, Contract.run, ContractResult.fst,
        Bind.bind, Pure.pure, Verity.bind, Verity.pure, h_not_zero, h_zero_val, h_y_zero,
        ceil_add_val_of_pos x y h_zero_val h_y_zero]

end proof.FixedPointMathLibProof
