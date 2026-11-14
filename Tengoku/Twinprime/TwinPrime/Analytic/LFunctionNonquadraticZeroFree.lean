import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionInducedBound
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLogDerivative
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaLogDerivative
import Tengoku.Twinprime.TwinPrime.Analytic.ZeroFreeArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit zero-free region for nonquadratic primitive characters

The character square is induced to its actual primitive character before
applying the one-sided bound. The principal zeta pole remains in the
three-four-one inequality. The case `χ ^ 2 = 1` is not covered here.
-/

noncomputable section

namespace TwinPrime.Analytic

/--
@isnad1 id=le.2h1v.s7.2de05594e2da from=translated src=- shape=aaf2d0a7 vocab=bf351edb
-/
theorem neg_zeta_logDerivative_real_le_pole_add_forty (σ : ℝ)
    (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 40 := by
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
  have hs : ‖(σ : ℂ) - 1‖ ≤ 1 / 8 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb := norm_neg_zeta_logDerivative_sub_pole_le_forty (σ : ℂ) hs1 hs
  have hr := (Complex.re_le_norm
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - 1 / ((σ : ℂ) - 1))).trans hb
  have hp : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [Complex.sub_re, hp] at hr
  linarith

def nonquadraticZeroFreeBudget (q : ℕ) (t : ℝ) : ℝ :=
  120 + 4 * primitiveLFunctionLogBudget q t + primitiveLFunctionLogBudget q (2 * t) + Real.log q

/--
@isnad1 id=le.0h2v.s4.204f02080268 from=translated src=- shape=787c1379 vocab=6a4fddc4
-/
theorem nonquadraticZeroFreeBudget_ge (q : ℕ) (t : ℝ) :
    120 ≤ nonquadraticZeroFreeBudget q t := by
  have hk := primitiveLFunctionLogBudget_nonneg q t
  have hk2 := primitiveLFunctionLogBudget_nonneg q (2 * t)
  have hq := Real.log_natCast_nonneg q
  unfold nonquadraticZeroFreeBudget
  linarith

end TwinPrime.Analytic
