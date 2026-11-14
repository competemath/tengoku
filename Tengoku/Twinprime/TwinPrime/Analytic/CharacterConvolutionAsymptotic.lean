import Tengoku.Twinprime.TwinPrime.Analytic.ZetaConvolutionAsymptotic
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductLSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual main terms for four-factor character convolutions

The finite hyperbola estimate is specialized to three nonprincipal character
factors. Ordered continuation identifies its main coefficient with the actual
product of their values at one. For the quadratic four-factor construction,
this is the value of its entire regularization at the zeta pole.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- An unconditional summatory error about the actual three-L-value product.
Every character factor is nonprincipal, but need not be primitive.-/
theorem norm_zeta_three_character_convolution_sub_LFunction_product_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory
      ((zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ₁ ·) *
        toArithmeticFunction (χ₂ ·) * toArithmeticFunction (χ₃ ·)) x -
      (x : ℂ) * (DirichletCharacter.LFunction χ₁ 1 *
        DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction χ₃ 1)‖ ≤
      (1 + 3250 * (q : ℝ) ^ 2) * x ^ (4 / 5 : ℝ) * (1 + Real.log x) ^ 2 := by
  let f : ArithmeticFunction ℂ := toArithmeticFunction (χ₁ ·) *
    toArithmeticFunction (χ₂ ·) * toArithmeticFunction (χ₃ ·)
  have hA (u : ℝ) (hu : 1 ≤ u) :
      ‖complexArithmeticSummatory f u‖ ≤ (130 * (q : ℝ) ^ 2) * u ^ (3 / 4 : ℝ) :=
    norm_three_character_convolution_summatory_le_power χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ u hu
  have hMass (u : ℝ) (hu : 1 ≤ u) :
      (∑ n ∈ Ioc 0 ⌊u⌋₊, ‖f n‖) ≤ u * (1 + Real.log u) ^ 2 :=
    sum_norm_three_character_convolution_le χ₁ χ₂ χ₃ u hu
  have hlimit : powerDirichletLimit f 1 =
      DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction χ₃ 1 :=
    powerDirichletLimit_three_character_convolution_eqOn χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃
      (by norm_num)
  have hcoef : f * (zeta : ArithmeticFunction ℂ) =
      (zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ₁ ·) *
        toArithmeticFunction (χ₂ ·) * toArithmeticFunction (χ₃ ·) := by
    dsimp [f]
    ac_rfl
  have h := norm_zeta_convolution_sub_powerDirichletLimit_le f (130 * (q : ℝ) ^ 2)
    (by positivity) hA hMass x hx
  rw [hcoef, hlimit] at h
  convert h using 1
  ring

/-- The main term of the actual quadratic-product coefficients is the
regularized value at one when all three character factors are nonprincipal.-/
theorem norm_quadraticProductCoefficients_summatory_sub_residue_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory (quadraticProductCoefficients χ₁ χ₂) x -
      (x : ℂ) * regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ ≤
      (1 + 3250 * (q : ℝ) ^ 2) * x ^ (4 / 5 : ℝ) * (1 + Real.log x) ^ 2 := by
  simpa only [quadraticProductCoefficients, regularizedQuadraticLFunctionProduct_one] using
    norm_zeta_three_character_convolution_sub_LFunction_product_le
      χ₁ χ₂ (χ₁ * χ₂) hχ₁ hχ₂ hχ₁₂ x hx

/-- Distinct nonprincipal quadratic characters meet the three nonprincipal
conditions. In fact only the first character's square-one identity is needed
for this analytic bound; positivity is a separate finite theorem.-/
theorem norm_quadraticProductCoefficients_summatory_sub_residue_le_of_distinct
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hsq : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory (quadraticProductCoefficients χ₁ χ₂) x -
      (x : ℂ) * regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ ≤
      (1 + 3250 * (q : ℝ) ^ 2) * x ^ (4 / 5 : ℝ) * (1 + Real.log x) ^ 2 :=
  norm_quadraticProductCoefficients_summatory_sub_residue_le χ₁ χ₂ hχ₁ hχ₂
    (quadratic_character_mul_ne_one_of_ne χ₁ χ₂ hsq hne) x hx

end TwinPrime.Analytic
