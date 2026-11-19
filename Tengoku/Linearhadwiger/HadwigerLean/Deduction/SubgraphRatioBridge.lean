import Tengoku.Linearhadwiger.HadwigerLean.Deduction.Theorem4Scale
import Tengoku.Linearhadwiger.HadwigerLean.Graph.SubgraphImageIso
import Tengoku.Linearhadwiger.HadwigerLean.Deduction.ExternalInputs
import Tengoku.Linearhadwiger.HadwigerLean.Deduction.SubgraphRatioNumerics
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ratio-set estimates for the final Theorem 4 comparison. -/

namespace HadwigerLean.Deduction

universe u

/-- The lower endpoint of the paper's scale window is no greater than `t`
for `t ≥ 3`.
@isnad1 id=le.1h1v.s5.f7d553d2d8f8 from=translated src=- shape=77d99d00 vocab=d5996e26
-/
theorem dp_window_le_self (t : ℕ) (ht : 3 ≤ t) :
    (t : ℝ) / Real.sqrt (Real.log (t : ℝ)) ≤ (t : ℝ) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlog : 1 ≤ Real.log (t : ℝ) := by
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    exact hlog3.trans (Real.log_le_log (by norm_num)
      (by exact_mod_cast ht))
  have hroot : 1 ≤ Real.sqrt (Real.log (t : ℝ)) :=
    (Real.one_le_sqrt).2 hlog
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hroot)).2
  nlinarith

end HadwigerLean.Deduction
