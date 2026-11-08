module
public import Tengoku.Seed.MeasureTheory.Integral.Gamma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Laplace-type integrals

This file evaluates basic Laplace integrals over `Set.Ioi (0 : ℝ)` that occur in the
"another integral" representations for `a'` and `b'`.

## Main statements
* `MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi`
* `MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi`
* `MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi`
-/

namespace MagicFunction.g.CohnElkies

open scoped BigOperators
open MeasureTheory Real

private lemma gamma_two : Real.Gamma (2 : ℝ) = 1 := by
  simp

lemma integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-a * t)) = 1 / a := by
  -- `p = 1` so `x ^ p = x`, and `Gamma 2 = 1`.
  simpa [Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg_one, one_div] using
    (integral_exp_neg_mul_rpow (p := (1 : ℝ)) (b := a) (hp := by norm_num) (hb := ha))

end MagicFunction.g.CohnElkies
