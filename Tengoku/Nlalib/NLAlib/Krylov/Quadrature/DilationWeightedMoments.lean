import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.DilationMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The weighted odd reduction of a rectangular dilation

The squared-variable pushforward of `x² dμ` for the actual dilation at `(u,0)` is
the right normal matrix's spectral measure at `Bᵀu`. This supplies the native measure
used by the odd orthogonal-polynomial reduction.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Rectangular multiplication intertwines all powers of the two normal matrices.-/
theorem pow_mul_transpose_mul_eq_mul_pow (B : Matrix m n ℝ) (k : ℕ) :
    (B * Bᵀ) ^ k * B = B * (Bᵀ * B) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc
      ((B * Bᵀ) ^ k * (B * Bᵀ)) * B =
          ((B * Bᵀ) ^ k * B) * (Bᵀ * B) := by simp only [Matrix.mul_assoc]
      _ = B * (Bᵀ * B) ^ k * (Bᵀ * B) := by rw [ih]
      _ = _ := Matrix.mul_assoc _ _ _

/-- The next left-normal moment is the right-normal moment at the transposed seed.-/
theorem dotProduct_pow_succ_left_normal_eq (B : Matrix m n ℝ) (u : m → ℝ) (k : ℕ) :
    u ⬝ᵥ ((B * Bᵀ) ^ (k + 1) *ᵥ u) =
      (Bᵀ *ᵥ u) ⬝ᵥ ((Bᵀ * B) ^ k *ᵥ (Bᵀ *ᵥ u)) := by
  have hp : (B * Bᵀ) ^ (k + 1) = B * ((Bᵀ * B) ^ k * Bᵀ) := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_transpose_mul_eq_mul_pow, Matrix.mul_assoc]
  rw [hp, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    ← Matrix.mulVec_mulVec]

end NLAlib
