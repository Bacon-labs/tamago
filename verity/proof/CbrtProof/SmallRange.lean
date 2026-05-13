import Mathlib.Tactic.IntervalCases
import CbrtProof.CbrtCorrect

/-
  Small cbrt range facts.

  The main cbrt proof handles x >= 256 through octave certificates. These facts
  close the remaining finite range using mathlib's bounded case splitter; each
  resulting concrete arithmetic goal is then checked by Lean's native evaluator.
-/

theorem innerCbrt_upper_of_lt_256 (x : Nat) (hx : x < 256) :
    innerCbrt x ≤ icbrt x + 1 := by
  interval_cases x <;> native_decide

theorem innerCbrt_on_perfect_cube_small (m : Nat) (hm : m < 256) :
    innerCbrt (m * m * m) = m := by
  interval_cases m <;> native_decide
