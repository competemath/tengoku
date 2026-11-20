import Tengoku.Lmlf.LMLF.Results.HypergeometricPrincipal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Public-use tests for principal Gauss exceptional-parameter results
-/

namespace LMLFTest.Results

open LMLF.Definitions LMLF.ODE

/-- A public consumer composing the principal exceptional shift, principal analyticity, and the
principal polynomial Gauss equation. It intentionally makes no exact vanishing-order claim when
the Pochhammer prefactor is zero.-/
theorem principalExceptionalGaussCertificate (a b : ℂ) (N : ℕ) :
    let H : ℂ → ℂ := fun z ↦
      ((ascPochhammer ℂ (N + 1)).eval a *
        (ascPochhammer ℂ (N + 1)).eval b) *
          regularizedGaussHypergeometric
            (a + ((N + 1 : ℕ) : ℂ))
            (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z
    Set.EqOn (regularizedGaussHypergeometric a b (-(N : ℂ)))
        (fun z ↦ z ^ (N + 1) * H z) gaussHypergeometricDomain ∧
      AnalyticOnNhd ℂ H gaussHypergeometricDomain ∧
      ∀ z ∈ gaussHypergeometricDomain,
        z * (1 - z) * deriv (deriv (regularizedGaussHypergeometric a b (-(N : ℂ)))) z +
            (-(N : ℂ) - (a + b + 1) * z) *
              deriv (regularizedGaussHypergeometric a b (-(N : ℂ))) z -
          a * b * regularizedGaussHypergeometric a b (-(N : ℂ)) z = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hshift := regularizedGaussHypergeometric_neg_nat (a := a) (b := b) N hz
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hshift
  · exact analyticOnNhd_const.mul
      (regularizedGaussHypergeometric_analyticOnNhd
        (a + ((N + 1 : ℕ) : ℂ))
        (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ))
  · intro z hz
    exact regularizedGaussHypergeometric_gaussEquation a b (-(N : ℂ)) hz

end LMLFTest.Results
