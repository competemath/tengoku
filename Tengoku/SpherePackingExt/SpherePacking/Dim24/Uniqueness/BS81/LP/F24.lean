module
public import Tengoku.Seed.Algebra.Polynomial.Basic
public import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
public import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The BS81 polynomial `f24` for the `(24, 1/2)` LP bound

This file defines the polynomial `f24` used in BS81 Theorem 13 and records basic evaluations and
the sign condition `f24.eval t ≤ 0` for `t ∈ [-1, 1/2]`.

## Main definitions
* `f24`

## Main statements
* `f24_eval`
* `f24_eval_one`
* `f24_eval_nonpos_of_mem_Icc`

## References
* `paper/BS81/sources.tex`, §4, Theorem 13
-/

namespace SpherePacking.Dim24.Uniqueness.BS81
noncomputable section

open Polynomial

/-- The BS81 polynomial used for the `(24, 1/2)` LP bound.-/
@[expose] public def f24 : Polynomial ℝ :=
  (X + C 1) *
    (X + C (1 / 2 : ℝ)) ^ 2 *
      (X + C (1 / 4 : ℝ)) ^ 2 *
        X ^ 2 *
          (X - C (1 / 4 : ℝ)) ^ 2 *
            (X - C (1 / 2 : ℝ))

/-- Expanded evaluation formula for `f24`.-/
@[simp] public lemma f24_eval (t : ℝ) :
    f24.eval t =
      (t + 1) *
        (t + (1 / 2 : ℝ)) ^ 2 *
          (t + (1 / 4 : ℝ)) ^ 2 *
            t ^ 2 *
              (t - (1 / 4 : ℝ)) ^ 2 *
                (t - (1 / 2 : ℝ)) := by
  simp [f24, mul_assoc, mul_left_comm, mul_comm]

end

end SpherePacking.Dim24.Uniqueness.BS81
