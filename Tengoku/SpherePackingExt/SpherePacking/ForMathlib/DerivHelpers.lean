module
public import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
public import Tengoku.Seed.Analysis.Complex.Exponential
public import Tengoku.Seed.Analysis.Complex.RealDeriv
public import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derivative helpers

This file collects small `HasDerivAt` and norm/inequality lemmas that get duplicated across the
project.
-/

namespace SpherePacking.ForMathlib

open scoped Complex

/-- If `x ∈ ball x₀ ε`, then `|x| ≤ |x₀| + ε`.-/
public lemma abs_le_abs_add_of_mem_ball {x x₀ ε : ℝ} (hx : x ∈ Metric.ball x₀ ε) :
    |x| ≤ |x₀| + ε := by
  have hdist : |x - x₀| ≤ ε := le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  have hx' : |x| ≤ |x₀| + |x - x₀| := by simpa [add_sub_cancel] using abs_add_le x₀ (x - x₀)
  exact hx'.trans (add_le_add_right hdist |x₀|)

/-- If `‖z‖ ≤ 2`, then `‖(π * I) * z‖ ≤ 2 * π`.-/
public lemma norm_mul_pi_I_le_two_pi {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖((Real.pi : ℂ) * (Complex.I : ℂ)) * z‖ ≤ 2 * Real.pi := by
  simpa [mul_assoc, abs_of_nonneg Real.pi_pos.le, mul_comm] using
    mul_le_mul_of_nonneg_left hz Real.pi_pos.le

/--
Bound `‖exp((x : ℂ) * c)‖` when `x ∈ ball x₀ 1` and `‖c‖ ≤ B`, by `exp((|x₀| + 1) * B)`.-/
public lemma norm_cexp_ofReal_mul_le_exp_mul_of_norm_le {x x₀ : ℝ} {c : ℂ} {B : ℝ}
    (hc : ‖c‖ ≤ B) (hx : x ∈ Metric.ball x₀ (1 : ℝ)) :
    ‖cexp ((x : ℂ) * c)‖ ≤ Real.exp ((|x₀| + 1) * B) := by
  have hxabs : |x| ≤ |x₀| + 1 := abs_le_abs_add_of_mem_ball hx
  have hre : ((x : ℂ) * c).re ≤ (|x₀| + 1) * B :=
    (Complex.re_le_norm _).trans <| by
      have : |x| * ‖c‖ ≤ (|x₀| + 1) * B := by gcongr
      simpa [norm_mul, Complex.norm_real, mul_assoc] using this
  simpa [Complex.norm_exp] using Real.exp_le_exp.2 hre

end SpherePacking.ForMathlib
