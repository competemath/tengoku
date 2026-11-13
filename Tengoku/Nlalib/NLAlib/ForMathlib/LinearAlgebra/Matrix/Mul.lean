import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Columns and entries of matrix products

* `col_mul_eq_mulVec_col`: column `j` of a product is the left factor applied to column `j`,
  `(M * N).col j = M *ᵥ N.col j`;
* `transpose_mul_mul_apply_eq_dotProduct`: entries of a compression,
  `(Uᵀ A V)ᵢⱼ = uᵢ ⬝ (A vⱼ)`.

Mathlib has no named form of either (the first holds by unfolding). Helpers for atlas
`block-krylov-subspace`, `arnoldi-def`, `arnoldi-relation` and
`golub-kahan-bidiagonalization`.
-/

open scoped Matrix

namespace NLAlib

/-- Column `j` of a product is the matrix applied to column `j`: `(M N) e_j = M (N e_j)`.
Stated over any non-unital non-associative semiring (covers `ℝ` and `ℂ`). Helper for
`block-krylov-subspace` and `arnoldi-relation`.
@isnad1 id=eq.0h7v.s6.fbe10fb5ab64 from=translated src=- shape=e9f835e5 vocab=b4c8660d
-/
theorem col_mul_eq_mulVec_col {α : Type*} [NonUnitalNonAssocSemiring α] {m n s : Type*}
    [Fintype n] (M : Matrix m n α) (N : Matrix n s α) (j : s) :
    (M * N).col j = M *ᵥ N.col j := by
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Entries of a rectangular compression: `(Uᵀ A V)_{ij} = uᵢ ⬝ (A vⱼ)` for the columns `uᵢ`
of `U` and `vⱼ` of `V` (the square case `U = V = Q` gives `(Qᵀ A Q)ᵢⱼ = qᵢᵀ A qⱼ`). Helper for
`arnoldi-def` and `golub-kahan-bidiagonalization`.
@isnad1 id=eq.0h10v.s7.487ebb49467f from=translated src=- shape=01748f93 vocab=370ecc73
-/
theorem transpose_mul_mul_apply_eq_dotProduct {α : Type*} [CommSemiring α]
    {m n k l : Type*} [Fintype m] [Fintype n]
    (U : Matrix m k α) (A : Matrix m n α) (V : Matrix n l α) (i : k) (j : l) :
    (Uᵀ * A * V) i j = U.col i ⬝ᵥ (A *ᵥ V.col j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Matrix.col,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end NLAlib
