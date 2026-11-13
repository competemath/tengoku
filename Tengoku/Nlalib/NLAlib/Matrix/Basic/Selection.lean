import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Column-selection matrices

`selectionMatrix s = [e_{s 0}, …, e_{s (k−1)}] ∈ ℝ^{n×k}` for a label sequence `s : Fin k → n`
(repeats allowed). Right multiplication selects columns (`mul_selectionMatrix`), left
multiplication by the transpose selects rows (`transpose_selectionMatrix_mul`). Used by column
Nyström / partial Cholesky (`nystrom_selectionMatrix`) and, transposed, as the row selector of
the SRHT sketches (`srhtSketch`, `srhtWithReplacementSketch`).
-/

open scoped Matrix

namespace NLAlib

variable {n : Type*} [DecidableEq n]

/-- The **column-selection matrix** `[e_{s 0}, …, e_{s (k−1)}] ∈ ℝ^{n×k}`, so that
`A (selectionMatrix s) = A(:,S)` (`mul_selectionMatrix`) and the Nyström approximation with this
test matrix is the column Nyström approximation `A(:,S) A(S,S)⁺ A(S,:)`. Its transpose is the
row selector `R` of a subsampled randomized Hadamard transform `√(n/k) R H D`.-/
def selectionMatrix {k : ℕ} (s : Fin k → n) : Matrix n (Fin k) ℝ :=
  Matrix.of fun i j => if i = s j then 1 else 0

/-- Entries of the transposed selection matrix (the row selector): `(Sᵀ)ₐⱼ = [j = s a]`.
@isnad1 id=eq.0h5v.s5.0e31ad857e85 from=translated src=- shape=53ddee42 vocab=ed9c0008
-/
theorem transpose_selectionMatrix_apply {k : ℕ} (s : Fin k → n) (a : Fin k) (j : n) :
    (selectionMatrix s)ᵀ a j = if j = s a then 1 else 0 := rfl

variable [Fintype n]

/-- Right multiplication by a selection matrix selects columns: `A (selectionMatrix s) = A(:,S)`.
@isnad1 id=eq.0h5v.s6.54957b1dfffd from=translated src=- shape=8e9f9d86 vocab=67568dad
-/
theorem mul_selectionMatrix {m : Type*} {k : ℕ} (A : Matrix m n ℝ) (s : Fin k → n) :
    A * selectionMatrix s = A.submatrix id s := by
  ext i j; simp [selectionMatrix, Matrix.mul_apply]

/-- Left multiplication by the transpose of a selection matrix selects rows:
`(selectionMatrix s)ᵀ A = A(S,:)`.
@isnad1 id=eq.0h5v.s6.a63f45b75950 from=translated src=- shape=6625427c vocab=6ae1a2a8
-/
theorem transpose_selectionMatrix_mul {m : Type*} [Fintype m] {k : ℕ} (A : Matrix n m ℝ)
    (s : Fin k → n) : (selectionMatrix s)ᵀ * A = A.submatrix s id := by
  ext i j; simp [selectionMatrix, Matrix.mul_apply]

end NLAlib
