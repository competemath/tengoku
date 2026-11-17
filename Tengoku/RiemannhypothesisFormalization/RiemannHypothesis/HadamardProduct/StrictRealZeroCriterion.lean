/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.ExponentialPrefactor
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.RealZeroSign
import Tengoku.Seed.Analysis.Calculus.Deriv.Star

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict real-zero criteria for genus-one products

This module adds the affine exponential factor occurring in the classical
Hadamard factorization. A real logarithmic derivative of the prefactor does
not affect the upper-half-plane imaginary-part inequality, so the strict
criterion is controlled exactly by the zero product.
-/

namespace OverflowResidueRH

open scoped ComplexConjugate

/-- An affine-exponential prefactor times a normalized genus-one product.-/
noncomputable def expAffineGenusOneProduct
    (C a b : ℂ) (zeroLoc : ℕ → ℂ) : ℂ → ℂ :=
  fun z =>
    C * Complex.exp (a + b * z) * infiniteHadamardProduct zeroLoc z

/-- A Schwarz-reflecting function has real totalized logarithmic derivative at
the origin. No nonvanishing assumption is needed for this general statement:
if the value at the origin is zero, totalized division makes the response zero.-/
theorem logDerivativeResponse_zero_im_eq_zero_of_schwarz
    (F : ℂ → ℂ) (h_schwarz : ∀ z : ℂ, F (star z) = star (F z)) :
    (logDerivativeResponse F 0).im = 0 := by
  have hfun : conj ∘ F ∘ conj = F := by
    funext z
    change star (F (star z)) = F z
    rw [h_schwarz]
    simp
  have hderiv_eq := congrArg (fun f : ℂ → ℂ => deriv f 0) hfun
  have hderiv_star : star (deriv F 0) = deriv F 0 := by
    rw [deriv_conj_conj] at hderiv_eq
    simpa using hderiv_eq
  have hvalue_star : star (F 0) = F 0 := by
    simpa using (h_schwarz 0).symm
  have hderiv_im : (deriv F 0).im = 0 :=
    Complex.conj_eq_iff_im.mp hderiv_star
  have hvalue_im : (F 0).im = 0 :=
    Complex.conj_eq_iff_im.mp hvalue_star
  simp [logDerivativeResponse, Complex.div_im, hderiv_im, hvalue_im]

end OverflowResidueRH
