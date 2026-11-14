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

/-- The value at the removed singularity is the derivative of the numerator.
@isnad1 id=eq.0h3v.s6.ab6432142bbe from=translated src=- shape=a79b5ff8 vocab=1a57cc6a
-/
@[simp] theorem centeredQuadraticLFunctionProduct_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ 1 =
      deriv (fun s => regularizedQuadraticLFunctionProduct χ₁ χ₂ s -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta s) 1 := by
  simp only [centeredQuadraticLFunctionProduct, dslope_same]

/--
@isnad1 id=differen.3h3v.s8.5e8363f28a42 from=translated src=- shape=cfb61c62 vocab=28e0efc0
-/
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

/--
@isnad1 id=differen.4h3v.s8.4e224e3a9d40 from=translated src=- shape=c329ed8e vocab=5e9f59d8
-/
theorem differentiable_centeredQuadraticLFunctionProduct_of_distinct
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hsq : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂) :
    Differentiable ℂ (centeredQuadraticLFunctionProduct χ₁ χ₂) :=
  differentiable_centeredQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂
    (quadratic_character_mul_ne_one_of_ne χ₁ χ₂ hsq hne)

/-- The numerator identity is valid even at one, where both sides vanish.
@isnad1 id=eq.0h4v.s6.0941d26e4bf7 from=translated src=- shape=4370f2a4 vocab=b2b92c02
-/
theorem mul_centeredQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) :
    (s - 1) * centeredQuadraticLFunctionProduct χ₁ χ₂ s =
      regularizedQuadraticLFunctionProduct χ₁ χ₂ s -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta s := by
  simpa only [centeredQuadraticLFunctionProduct, smul_eq_mul, regularizedRiemannZeta_one,
    mul_one, sub_self, sub_zero] using
    sub_smul_dslope (fun z => regularizedQuadraticLFunctionProduct χ₁ χ₂ z -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * regularizedRiemannZeta z) 1 s

/-- The centering has its exact analytic formula away from one.
@isnad1 id=eq.1h4v.s6.f06a8ac737a3 from=translated src=- shape=177fe5be vocab=fc1b461a
-/
theorem centeredQuadraticLFunctionProduct_eq_of_ne_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) (hs : s ≠ 1) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ s = quadraticLFunctionProduct χ₁ χ₂ s -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta s := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs)
  rw [mul_centeredQuadraticLFunctionProduct,
    regularizedQuadraticLFunctionProduct_eq χ₁ χ₂ s hs,
    regularizedRiemannZeta_apply_of_ne_one s hs]
  ring

/--
@isnad1 id=eq.2h4v.s6.9710303d7d16 from=translated src=- shape=66aa626c vocab=efdcfd34
-/
theorem centeredQuadraticLFunctionProduct_eq_of_product_eq_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hzero : quadraticLFunctionProduct χ₁ χ₂ s = 0) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ s =
      -(regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta s) := by
  rw [centeredQuadraticLFunctionProduct_eq_of_ne_one χ₁ χ₂ s hs, hzero, zero_sub]

/-- An actual zero of the first character factor supplies a product zero.
@isnad1 id=eq.2h4v.s6.374afb902a36 from=translated src=- shape=f1d95f24 vocab=9669c042
-/
theorem centeredQuadraticLFunctionProduct_eq_of_LFunction_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hzero : DirichletCharacter.LFunction χ₁ s = 0) :
    centeredQuadraticLFunctionProduct χ₁ χ₂ s =
      -(regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta s) := by
  apply centeredQuadraticLFunctionProduct_eq_of_product_eq_zero χ₁ χ₂ s hs
  simp only [quadraticLFunctionProduct, hzero, mul_zero, zero_mul]

end TwinPrime.Analytic
