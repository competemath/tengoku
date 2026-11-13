import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.LinearAlgebra.Complex.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial intertwining of rectangular matrices

Polynomial functional calculus preserves an intertwining relation `B * A = A * C`.
This provides the rectangular Gram identity used by polynomial-filter range finding.
-/

noncomputable section

open Polynomial
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Powers preserve rectangular intertwining. Source: the induction in the manuscript
`sa:filter`, used for the polynomial-filter-range-finder target.
@isnad1 id=eq.1h7v.s7.ab11133c7db4 from=translated src=- shape=3d49029a vocab=888d83cf
-/
theorem pow_mul_eq_mul_pow_of_mul_eq {𝕜 : Type*} [Semiring 𝕜]
    {B : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : B * A = A * C) (j : ℕ) : B ^ j * A = A * C ^ j := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [pow_succ', Matrix.mul_assoc, hj, ← Matrix.mul_assoc, h, Matrix.mul_assoc,
      ← pow_succ']

/-- Polynomial calculus preserves rectangular intertwining: `BA = AC` implies
`p(B) A = A p(C)` for every polynomial `p`. Source: the manuscript `sa:filter`; Horn–Johnson
(2013), Lemma 2.4.4.0; standard polynomial functional calculus.
atlas: sylvester-equation
@isnad1 id=eq.1h8v.s8.5ec061173a65 from=translated src=- shape=ab9a581e vocab=4d2e89df
-/
theorem aeval_mul_eq_mul_aeval_of_mul_eq {R 𝕜 : Type*}
    [CommSemiring R] [CommSemiring 𝕜] [Algebra R 𝕜]
    {B : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : B * A = A * C) (p : R[X]) :
    aeval B p * A = A * aeval C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial j c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul]
    rw [pow_mul_eq_mul_pow_of_mul_eq h j]

/-- The two rectangular Gram polynomials intertwine through the original matrix.
Source: the manuscript `sa:filter`, its displayed polynomial-intertwining identity.
@isnad1 id=eq.0h4v.s8.37cde469976e from=translated src=- shape=6ceba972 vocab=c3dbc68d
-/
theorem aeval_gram_mul_eq_mul_aeval_gram (A : Matrix m n ℝ) (p : ℝ[X]) :
    aeval (A * Aᵀ) p * A = A * aeval (Aᵀ * A) p :=
  aeval_mul_eq_mul_aeval_of_mul_eq (Matrix.mul_assoc _ _ _) p

/-- Complex rectangular Gram polynomials intertwine through the original matrix.
Source: manuscript `sa:filter`, its complex `A A*`/`A* A` identity. The polynomial
has real coefficients, as in the manuscript.
@isnad1 id=eq.0h4v.s8.c912ee1786d8 from=translated src=- shape=2d283aed vocab=8594ab0d
-/
theorem aeval_conjGram_mul_eq_mul_aeval_conjGram (A : Matrix m n ℂ) (p : ℝ[X]) :
    aeval (A * Aᴴ) p * A = A * aeval (Aᴴ * A) p :=
  aeval_mul_eq_mul_aeval_of_mul_eq (Matrix.mul_assoc _ _ _) p

end NLAlib
