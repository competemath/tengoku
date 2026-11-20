import Tengoku.Lmlf.LMLF.ODE.Hypergeometric.Principal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Public-use tests for the principal Gauss hypergeometric function

The chart domains and the four IVP selections are intentionally private. Their geometry is
therefore checked by the production proofs that establish the public domain, disk agreement,
analyticity, and the equation on points representing every chart and both nonreal components.
-/

open Filter Metric Set
open scoped ComplexOrder Topology

namespace LMLFTest.ODE.Hypergeometric.Principal

open LMLF.Definitions LMLF.ODE

/-- Regression for the nonzero off-domain fallback: the terminating regularized series with
`a = b = 0`, `c = 1` is the constant one at every ambient point.
@isnad1 id=eq.0h1v.s4.e4b04965c61c from=translated src=- shape=dd6c531f vocab=0ffdff85
-/
theorem terminatingRegularizedGaussSeries_zero_zero_one (z : ℂ) :
    regularizedGaussHypergeometricSeriesSum 0 0 1 z = 1 := by
  change (Complex.regularizedGaussHGFunSeries 0 0 1).sum z = 1
  unfold FormalMultilinearSeries.sum
  rw [tsum_eq_single 0]
  · simp [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Complex.coeff_regularizedGaussHGFunSeries]
  · intro k hk
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Complex.coeff_regularizedGaussHGFunSeries]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hpoch : (ascPochhammer ℂ k).eval (0 : ℂ) = 0 := by
      rw [ascPochhammer_eval_eq_zero_iff]
      exact ⟨0, hkpos, by simp⟩
    simp [hpoch]

/-- Named boundary regression guarding against the obsolete zero fallback.
@isnad1 id=and.0h0v.s6.4cbea8bd26bf from=translated src=- shape=4c0ab75b vocab=f8bac9e9
-/
theorem terminatingPrincipalGauss_at_one :
    regularizedGaussHypergeometric 0 0 1 1 = 1 ∧
      gaussHypergeometric 0 0 1 1 = 1 := by
  have hfallback := regularizedGaussHypergeometric_eqOn_seriesSum_compl
    (0 : ℂ) 0 1 (show (1 : ℂ) ∈ gaussHypergeometricDomainᶜ by simp)
  have hregularized : regularizedGaussHypergeometric 0 0 1 1 = 1 :=
    hfallback.trans (terminatingRegularizedGaussSeries_zero_zero_one 1)
  refine ⟨hregularized, ?_⟩
  rw [gaussHypergeometric, hregularized, Complex.Gamma_one, one_mul]

end LMLFTest.ODE.Hypergeometric.Principal
