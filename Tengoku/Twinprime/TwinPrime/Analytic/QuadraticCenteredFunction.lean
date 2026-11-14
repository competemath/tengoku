import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductLSeries
import Tengoku.Seed.Analysis.Complex.RemovableSingularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An entire centered four-factor function

The actual regularized value at one is removed by subtracting that value
times regularized zeta. The numerator vanishes at one. When all three
character factors are nonprincipal, `dslope` gives its holomorphic quotient
by `s - 1`. Away from one this is exactly the four-factor product minus
its residue times zeta.
-/

noncomputable section

open scoped Topology

namespace TwinPrime.Analytic

def centeredQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  dslope (fun s => regularizedQuadraticLFunctionProduct χ₁ χ₂ s -
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta s) 1

/-- The value at the removed singularity is the derivative of the numerator.-/
@[simp] theorem centeredQuadraticLFunctionProduct_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ 1 =
      deriv (fun s => regularizedQuadraticLFunctionProduct χ₁ χ₂ s -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta s) 1 := by
  simp only [centeredQuadraticLFunctionProduct, dslope_same]

theorem differentiable_centeredQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    Differentiable ℂ (centeredQuadraticLFunctionProduct χ₁ χ₂) := by
  apply differentiableOn_univ.mp
  apply (Complex.differentiableOn_dslope (s := Set.univ) (c := (1 : ℂ))
    (by simp)).mpr
  exact ((differentiable_regularizedQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂ hχ₁₂).sub
    (differentiable_regularizedRiemannZeta.const_mul
      (regularizedQuadraticLFunctionProduct χ₁ χ₂ 1))).differentiableOn

theorem differentiable_centeredQuadraticLFunctionProduct_of_distinct
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hsq : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂) :
    Differentiable ℂ (centeredQuadraticLFunctionProduct χ₁ χ₂) :=
  differentiable_centeredQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂
    (quadratic_character_mul_ne_one_of_ne χ₁ χ₂ hsq hne)

/-- The numerator identity is valid even at one, where both sides vanish.-/
theorem mul_centeredQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) :
    (s - 1) * centeredQuadraticLFunctionProduct χ₁ χ₂ s =
      regularizedQuadraticLFunctionProduct χ₁ χ₂ s -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta s := by
  simpa only [centeredQuadraticLFunctionProduct, smul_eq_mul, regularizedRiemannZeta_one,
    mul_one, sub_self, sub_zero] using
    sub_smul_dslope (fun z => regularizedQuadraticLFunctionProduct χ₁ χ₂ z -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta z) 1 s

/-- The centering has its exact analytic formula away from one.-/
theorem centeredQuadraticLFunctionProduct_eq_of_ne_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) (hs : s ≠ 1) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ s = quadraticLFunctionProduct χ₁ χ₂ s -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta s := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs)
  rw [mul_centeredQuadraticLFunctionProduct,
    regularizedQuadraticLFunctionProduct_eq χ₁ χ₂ s hs,
    regularizedRiemannZeta_apply_of_ne_one s hs]
  ring

theorem centeredQuadraticLFunctionProduct_eq_of_product_eq_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hzero : quadraticLFunctionProduct χ₁ χ₂ s = 0) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ s =
      -(regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta s) := by
  rw [centeredQuadraticLFunctionProduct_eq_of_ne_one χ₁ χ₂ s hs, hzero, zero_sub]

/-- An actual zero of the first character factor supplies a product zero.-/
theorem centeredQuadraticLFunctionProduct_eq_of_LFunction_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hzero : DirichletCharacter.LFunction χ₁ s = 0) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ s =
      -(regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta s) := by
  apply centeredQuadraticLFunctionProduct_eq_of_product_eq_zero χ₁ χ₂ s hs
  simp only [quadraticLFunctionProduct, hzero, mul_zero, zero_mul]

end TwinPrime.Analytic
