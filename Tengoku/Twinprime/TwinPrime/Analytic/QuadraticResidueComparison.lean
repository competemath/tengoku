import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticCenteredContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaRealTruncation
import Tengoku.Twinprime.TwinPrime.Analytic.ResidueCutoff
import Tengoku.Twinprime.TwinPrime.Analytic.ResidueConductorBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative comparison with the actual quadratic-product residue

Subtracting the residue from the coefficients gives a convergent ordered
series below one. Its tail, the actual zeta truncation, and finite coefficient
positivity imply a residue lower bound at an actual real zero of the product.
The common-modulus and three nonprincipal conditions remain explicit.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- A weighted comparison retaining the actual product value and zeta term.-/
theorem norm_quadraticProductPartialSum_sub_product_sub_residue_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1) :
    ‖quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M -
      quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
        ((∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ))‖ ≤
      18522 * (1 + 3250 * (q : ℝ) ^ 2) * (M : ℝ) ^ (-(1 / 20 : ℝ)) := by
  have h := norm_centeredQuadraticLFunctionProduct_real_sub_partialSum_le
    χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ M hM β hβ hβ1.le
  rw [centeredQuadraticLFunctionProduct_eq_of_ne_one χ₁ χ₂ (β : ℂ)
    (by exact_mod_cast (ne_of_lt hβ1)),
    powerDirichletPartialSum_centeredQuadraticProductCoefficients] at h
  have heq : quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta (β : ℂ) -
      (quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
          (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ)))) =
      -(quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M -
        quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
          ((∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ))) := by ring
  rwa [heq, norm_neg] at h

end TwinPrime.Analytic
