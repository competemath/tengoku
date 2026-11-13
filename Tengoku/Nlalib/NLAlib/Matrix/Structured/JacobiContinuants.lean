import Tengoku.Nlalib.NLAlib.Matrix.Structured.JacobiAlgebra
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite polynomial Jacobi denominators

The finite continuant recurrence computes the actual characteristic polynomial of
the Jacobi coefficient matrix. These are the denominator polynomials of the finite
continued fractions; determinant quotients keep real intermediate poles explicit.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix

namespace NLAlib

/-- The finite Jacobi denominator continuant, with empty denominator one and
one-level denominator `X-a₀`. Coefficient shifts produce its trailing-block recurrence.-/
def jacobiContinuant {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) : ℕ → 𝕜[X]
  | 0 => 1
  | 1 => X - C (a 0)
  | n + 2 => (X - C (a 0)) *
      jacobiContinuant (fun i => a (i + 1)) (fun i => β (i + 1)) (n + 1) -
      C (β 1 ^ 2) * jacobiContinuant (fun i => a (i + 2)) (fun i => β (i + 2)) n

/-- The empty Jacobi characteristic denominator is one.
Source: operator derivations (OF26).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial)
@isnad1 id=eq.0h3v.s5.04be63939672 from=translated src=- shape=2b1c5e87 vocab=d5aa045c
-/
@[simp] theorem jacobiContinuant_zero {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) :
    jacobiContinuant a β 0 = 1 := rfl

/-- The finite denominator continuant evaluates to the actual shifted determinant,
over any coefficient field and including the empty order-zero system.
Source: operator derivations (OF26).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial)
@isnad1 id=eq.0h5v.s7.128e4d5fd583 from=translated src=- shape=d37e9a5c vocab=052155d8
-/
theorem eval_jacobiContinuant_eq_det {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (n : ℕ)
    (x : 𝕜) : (jacobiContinuant a β n).eval x =
      (x • (1 : Matrix (Fin n) (Fin n) 𝕜) - jacobiMatrix a β n).det := by
  induction n using Nat.twoStepInduction generalizing a β with
  | zero => simp [jacobiContinuant]
  | one => simp [jacobiContinuant, jacobiMatrix]
  | more n ih ih1 =>
    simp only [jacobiContinuant, eval_sub, eval_mul, eval_X, eval_C,
      ih, ih1, det_smul_one_sub_jacobiMatrix]

/-- The finite Jacobi continued-fraction denominator is the actual monic matrix
characteristic polynomial. Source: Gautschi (2004), Theorem 1.34; (OF26).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial)
@isnad1 id=eq.0h4v.s5.d9bb82f6c289 from=translated src=- shape=013918a6 vocab=45341260
-/
theorem charpoly_jacobiMatrix_eq_jacobiContinuant {𝕜 : Type*} [Field 𝕜] [Infinite 𝕜]
    (a β : ℕ → 𝕜) (n : ℕ) : (jacobiMatrix a β n).charpoly = jacobiContinuant a β n := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, eval_jacobiContinuant_eq_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

/-- Every finite Jacobi denominator is monic of its exact finite order.
Source: Gautschi (2004), Theorem 1.34.
@isnad1 id=monic.0h4v.s5.082b56c8c89f from=translated src=- shape=7e557450 vocab=2b4db3f2
-/
theorem monic_jacobiContinuant {𝕜 : Type*} [Field 𝕜] [Infinite 𝕜]
    (a β : ℕ → 𝕜) (n : ℕ) : (jacobiContinuant a β n).Monic := by
  rw [← charpoly_jacobiMatrix_eq_jacobiContinuant]
  exact Matrix.charpoly_monic _

end NLAlib
