import Tengoku.Lmlf.LMLF.Results.Hypergeometric
import Tengoku.Lmlf.LMLF.ODE.Hypergeometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Public-use tests for exceptional Gauss hypergeometric denominator shifts
-/

namespace LMLFTest.Results

open LMLF.Definitions LMLF.ODE

/-- A focused consumer combining the all-parameter Gauss equation with the exceptional
factorization and the analytic, nonvanishing residual factor that certifies exponent `N + 1`.
@isnad1 id=other.1h3v.s9.58ca275793f4 from=translated src=- shape=dfb7df25 vocab=4d15d336
-/
theorem exceptionalGaussExponentCertificate
    {a b : ℂ} (N : ℕ)
    (hpref : (ascPochhammer ℂ (N + 1)).eval a *
      (ascPochhammer ℂ (N + 1)).eval b ≠ 0) :
    let H : ℂ → ℂ := fun z ↦
      ((ascPochhammer ℂ (N + 1)).eval a *
        (ascPochhammer ℂ (N + 1)).eval b) *
          regularizedGaussHypergeometricSeriesSum
            (a + ((N + 1 : ℕ) : ℂ))
            (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z
    Set.EqOn
        (regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ)))
        (fun z ↦ z ^ (N + 1) * H z) (Metric.ball 0 1) ∧
      AnalyticOnNhd ℂ H (Metric.ball 0 1) ∧
      H 0 ≠ 0 ∧
      ∀ {z : ℂ}, ‖z‖ < 1 →
        z * (1 - z) *
              deriv (deriv (regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ)))) z
          + (-(N : ℂ) - (a + b + 1) * z) *
              deriv (regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ))) z
          - a * b * regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ)) z = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have hfactor := regularizedGaussHypergeometricSeriesSum_neg_nat
      (a := a) (b := b) N (by simpa using hz)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hfactor
  · exact analyticOnNhd_const.mul
      (regularizedGaussHypergeometricSeriesSum_analyticOnNhd
        (a + ((N + 1 : ℕ) : ℂ))
        (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ))
  · have hfac : (Nat.factorial (N + 1) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hgamma : Complex.Gamma (((N + 2 : ℕ) : ℂ)) =
        (Nat.factorial (N + 1) : ℂ) := by
      rw [show ((N + 2 : ℕ) : ℂ) = ((N + 1 : ℕ) : ℂ) + 1 by
        push_cast
        ring]
      exact Complex.Gamma_nat_eq_factorial (N + 1)
    rw [regularizedGaussHypergeometricSeriesSum_zero, hgamma]
    exact mul_ne_zero hpref (inv_ne_zero hfac)
  · intro z hz
    exact regularizedGaussHypergeometricSeriesSum_gaussEquation hz

end LMLFTest.Results
