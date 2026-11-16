/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.Algebra.Polynomial.Derivative
import Tengoku.Seed.RingTheory.Polynomial.Wronskian
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A two-dimensional obstruction for maps affine in one variable

Consider a plane polynomial map

`G(x, y) = (a(x) * y + b(x), c(x) * y + d(x))`.

Its Jacobian determinant is affine in `y`; its two coefficients are

`a' * c - a * c'` and `b' * c - a * d'`.

This module proves that if the determinant is a nonzero constant, then both
`a'` and `c'` vanish. Over a characteristic-zero field, `a` and `c` are
therefore constants. Thus a two-dimensional counterexample cannot arise from
this direct analogue of the announced three-dimensional map's affine-in-`z`
shape.

## Main results

- `affineInY_slopes_derivative_eq_zero`: the `y`-slopes have zero derivative.
- `affineInY_slopes_constant`: in characteristic zero, those slopes are
  constant polynomials.
- `affineInY_injective`: the resulting plane map is injective.
-/

noncomputable section

open scoped Polynomial

namespace JacobianTwo.AffineInOneVariable

open Polynomial

variable {K : Type*} [Field K]

/-- The Jacobian determinant of
`(a(x) * y + b(x), c(x) * y + d(x))`, represented as a polynomial in `y`
whose coefficients are polynomials in `x`.-/
def affineInYJacobian (a b c d : K[X]) : (K[X])[X] :=
  C (derivative a * c - a * derivative c) * X +
    C (derivative b * c - a * derivative d)

/-- The plane polynomial map represented by four one-variable polynomials.-/
def affineInYMap (a b c d : K[X]) (p : K × K) : K × K :=
  (a.eval p.1 * p.2 + b.eval p.1, c.eval p.1 * p.2 + d.eval p.1)

/--
@isnad1 id=eq.0h5v.s9.0fa05d6e6795 from=translated src=- shape=5a81282e vocab=ab0cea3f
-/
@[simp]
theorem coeff_one_affineInYJacobian (a b c d : K[X]) :
    (affineInYJacobian a b c d).coeff 1 = derivative a * c - a * derivative c := by
  simp [affineInYJacobian]

/--
@isnad1 id=eq.0h5v.s9.872479d46bd0 from=translated src=- shape=4d681dba vocab=ab0cea3f
-/
@[simp]
theorem coeff_zero_affineInYJacobian (a b c d : K[X]) :
    (affineInYJacobian a b c d).coeff 0 = derivative b * c - a * derivative d := by
  simp [affineInYJacobian]

/-- If an affine-in-`y` plane map has nonzero constant Jacobian determinant,
then the derivatives of both `y`-slope polynomials vanish.
@isnad1 id=and.2h6v.s10.1d7733c61616 from=translated src=- shape=e177a547 vocab=169f1280
-/
theorem affineInY_slopes_derivative_eq_zero {a b c d : K[X]} {k : K}
    (hk : k ≠ 0)
    (hdet : affineInYJacobian a b c d = C (C k)) :
    derivative a = 0 ∧ derivative c = 0 := by
  have hy : derivative a * c - a * derivative c = 0 := by
    have h := congrArg (fun p : (K[X])[X] ↦ p.coeff 1) hdet
    simpa using h
  have hconst : derivative b * c - a * derivative d = C k := by
    have h := congrArg (fun p : (K[X])[X] ↦ p.coeff 0) hdet
    simpa using h
  have hac : IsCoprime a c := by
    refine ⟨-C (k⁻¹) * derivative d, C (k⁻¹) * derivative b, ?_⟩
    calc
      (-C (k⁻¹) * derivative d) * a + (C (k⁻¹) * derivative b) * c =
          C (k⁻¹) * (derivative b * c - a * derivative d) := by ring
      _ = C (k⁻¹) * C k := by rw [hconst]
      _ = 1 := by rw [← C_mul]; simp [hk]
  apply hac.wronskian_eq_zero_iff.mp
  calc
    wronskian a c = -(derivative a * c - a * derivative c) := by
      simp only [wronskian]
      ring
    _ = 0 := by rw [hy, neg_zero]

/-- Over a characteristic-zero field, the two `y`-slope polynomials in a
constant-Jacobian affine-in-`y` map are constant.
@isnad1 id=and.2h6v.s9.a98b114754fe from=translated src=- shape=c86bbc97 vocab=7b813310
-/
theorem affineInY_slopes_constant [CharZero K] {a b c d : K[X]} {k : K}
    (hk : k ≠ 0)
    (hdet : affineInYJacobian a b c d = C (C k)) :
    a = C (a.coeff 0) ∧ c = C (c.coeff 0) := by
  obtain ⟨ha, hc⟩ := affineInY_slopes_derivative_eq_zero hk hdet
  exact ⟨eq_C_of_derivative_eq_zero ha, eq_C_of_derivative_eq_zero hc⟩

/-- A plane map that is affine in one variable and has nonzero constant
Jacobian determinant is injective over every characteristic-zero field. This
rules out a noninjective Keller map within the entire ansatz.
@isnad1 id=injectiv.2h6v.s8.04316766bbf9 from=translated src=- shape=4f7fc65e vocab=0bbbe56a
-/
theorem affineInY_injective [CharZero K] {a b c d : K[X]} {k : K}
    (hk : k ≠ 0)
    (hdet : affineInYJacobian a b c d = C (C k)) :
    Function.Injective (affineInYMap a b c d) := by
  let alpha := a.coeff 0
  let gamma := c.coeff 0
  obtain ⟨ha, hc⟩ := affineInY_slopes_constant hk hdet
  have hconst : derivative b * c - a * derivative d = C k := by
    have h := congrArg (fun p : (K[X])[X] ↦ p.coeff 0) hdet
    simpa using h
  have hconst' : derivative b * C gamma - C alpha * derivative d = C k := by
    dsimp [alpha, gamma]
    rw [ha, hc] at hconst
    exact hconst
  let e := C gamma * b - C alpha * d
  have he_derivative : derivative e = C k := by
    simp only [e, derivative_sub, derivative_C_mul]
    simpa [mul_comm] using hconst'
  have he_linear : e - C k * X = C ((e - C k * X).coeff 0) := by
    apply eq_C_of_derivative_eq_zero
    rw [derivative_sub, he_derivative, derivative_C_mul_X, sub_self]
  have hslopes : alpha ≠ 0 ∨ gamma ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have hcoeff := congrArg (fun p : K[X] ↦ p.coeff 0) hconst'
    simp [h.1, h.2] at hcoeff
    exact hk hcoeff.symm
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hmaps
  have hfirst := congrArg Prod.fst hmaps
  have hsecond := congrArg Prod.snd hmaps
  simp only [affineInYMap] at hfirst hsecond
  rw [ha] at hfirst
  rw [hc] at hsecond
  simp only [eval_C] at hfirst hsecond
  change alpha * y₁ + b.eval x₁ = alpha * y₂ + b.eval x₂ at hfirst
  change gamma * y₁ + d.eval x₁ = gamma * y₂ + d.eval x₂ at hsecond
  have he_eval : e.eval x₁ = e.eval x₂ := by
    simp only [e, eval_sub, eval_mul, eval_C]
    linear_combination gamma * hfirst - alpha * hsecond
  have he_affine : e.eval x₁ - k * x₁ = e.eval x₂ - k * x₂ := by
    have hx₁ := congrArg (eval x₁) he_linear
    have hx₂ := congrArg (eval x₂) he_linear
    simp only [eval_sub, eval_mul, eval_C, eval_X] at hx₁ hx₂
    exact hx₁.trans hx₂.symm
  have hkx : k * x₁ = k * x₂ := by
    linear_combination he_eval - he_affine
  have hx : x₁ = x₂ := (mul_left_cancel₀ hk) hkx
  subst x₂
  have hy : y₁ = y₂ := by
    rcases hslopes with halpha | hgamma
    · apply (mul_left_cancel₀ halpha)
      exact add_right_cancel hfirst
    · apply (mul_left_cancel₀ hgamma)
      exact add_right_cancel hsecond
  subst y₂
  rfl

end JacobianTwo.AffineInOneVariable
