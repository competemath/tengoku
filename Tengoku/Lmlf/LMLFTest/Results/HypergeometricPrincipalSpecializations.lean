import Tengoku.Lmlf.LMLF.Results.HypergeometricPrincipalSpecializations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Public-use tests for principal Gauss hypergeometric specializations
-/

namespace LMLFTest.Results

open LMLF.Definitions

/-- A public consumer combining the principal specialization, the `Gamma(1)` convention bridge,
and the geometric-series API on its convergence disk.-/
theorem principalGaussSpecializationConventionSeriesCertificate
    (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    gaussHypergeometric a 1 1 z = (1 - z) ^ (-a) ∧
      regularizedGaussHypergeometric a 1 1 z = (1 - z) ^ (-a) ∧
      gaussHypergeometric a 1 1 z = regularizedGaussHypergeometric a 1 1 z ∧
      HasSum (fun n : ℕ ↦ z ^ n) (gaussHypergeometric 1 1 1 z) := by
  have hzDomain : z ∈ gaussHypergeometricDomain := by
    rw [mem_gaussHypergeometricDomain_iff]
    right
    exact lt_of_le_of_lt (Complex.re_le_norm z) hz
  have hquotient := gaussHypergeometric_div_Gamma a 1 1 (fun n ↦ by
    intro h
    have hreal := congrArg Complex.re h
    have hn : (0 : ℝ) ≤ n := by positivity
    norm_num at hreal
    linarith) z
  rw [Complex.Gamma_one, div_one] at hquotient
  exact ⟨gaussHypergeometric_one_one a hzDomain,
    regularizedGaussHypergeometric_one_one a hzDomain, hquotient,
    hasSum_gaussHypergeometric_geometric hz⟩

end LMLFTest.Results
