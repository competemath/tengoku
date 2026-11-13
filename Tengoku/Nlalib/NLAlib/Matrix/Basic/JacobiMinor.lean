import Tengoku.Nlalib.NLAlib.Matrix.Basic.JacobiBlockMinor
import Tengoku.Nlalib.NLAlib.Matrix.Basic.SchurRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Signed Jacobi inverse-minor identity

Row and column splitting bijections encode equal-sized selected index sets
and their complements. The relative permutation sign is the cofactor sign.
All subminors, including singular, empty and full minors, are covered.
Horn–Johnson 2013, §§0.7.6 and 0.8.4; complementary-nullities.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
/-- Two coordinate bijections change a determinant by their relative
permutation sign. This is the cofactor orientation convention for Jacobi's
identity. Horn–Johnson 2013, §0.8.4.
@isnad1 id=eq.0h5v.s7.3787428cb19d from=translated src=- shape=0db3c239 vocab=57ae2ca2
-/
theorem det_submatrix_equiv_eq_sign_mul {n r : Type*}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (A : Matrix n n ℝ) (er ec : r ≃ n) :
    (A.submatrix er ec).det =
      (Equiv.Perm.sign (ec.trans er.symm) : ℝ) * A.det := by
  have h : A.submatrix er ec = (A.submatrix er er).submatrix id (ec.trans er.symm) := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.apply_symm_apply, id_eq]
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

universe u v w

end NLAlib
