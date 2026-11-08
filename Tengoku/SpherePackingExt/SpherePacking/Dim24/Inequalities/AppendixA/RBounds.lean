module
public import Tengoku.Seed.Analysis.Normed.Algebra.Exponential
public import Tengoku.Seed.Analysis.Real.Pi.Bounds
public import Tengoku.Seed.Data.Nat.Factorial.Basic
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.NormNum.BigOperators
import Tengoku.Seed.Tactic.NormNum.NatFactorial
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Elementary bounds for `r(t) = exp(-π t)` used in Appendix A truncation arguments.

We keep these lemmas in a dedicated file to avoid duplicating the `exp`/`π` numerics across the
various truncation modules.
-/

open scoped Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The `r`-parameter used in Appendix A: `r(t) = exp(-π t)`.-/
@[expose] public def r (t : ℝ) : ℝ := Real.exp (-Real.pi * t)

private lemma exp_pi_gt_23 : (23 : ℝ) < Real.exp (157 / 50 : ℝ) := by
  have hsum_le :
      (Finset.sum (Finset.range 10) fun n : ℕ => (157 / 50 : ℝ) ^ n / (Nat.factorial n)) ≤
        Real.exp (157 / 50 : ℝ) := by
    have hx : (0 : ℝ) ≤ (157 / 50 : ℝ) := by norm_num
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      exp_lower_bound_range (x := (157 / 50 : ℝ)) hx 9
  have hsum_gt :
      (23 : ℝ) <
        Finset.sum (Finset.range 10) fun n : ℕ => (157 / 50 : ℝ) ^ n / (Nat.factorial n) := by
    -- A closed numerical inequality.
    set_option maxRecDepth 6000 in
    norm_num
  exact lt_of_lt_of_le hsum_gt hsum_le

private lemma exp_pi_gt_23' : (23 : ℝ) < Real.exp Real.pi := by
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    simpa [show (3.14 : ℝ) = (157 / 50 : ℝ) by norm_num] using Real.pi_gt_d2
  exact exp_pi_gt_23.trans (Real.exp_lt_exp.2 hpi)

private lemma t_le_exp_pi_mul_sub_one (t : ℝ) (ht : 1 ≤ t) :
    t ≤ Real.exp (Real.pi * (t - 1)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ht1 : 0 ≤ t - 1 := sub_nonneg.2 ht
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_d2]
  have hlog : Real.log t ≤ Real.pi * (t - 1) := by
    refine (Real.log_le_sub_one_of_pos ht0).trans ?_
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hpi ht1)
  simpa [Real.exp_log ht0] using (Real.exp_le_exp.2 hlog)

end

end SpherePacking.Dim24.AppendixA
