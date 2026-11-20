import Tengoku.Hellingerrepolean4.Hellinger.TraceNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.TraceNorm

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/--
@isnad1 id=eq.0h4v.s7.da9944b8da92 from=translated src=- shape=aeef007e vocab=d60763b8
-/
theorem abs_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    CFC.abs (A.submatrix e e) = (CFC.abs A).submatrix e e := by
  apply CFC.sqrt_unique
  · rw [Matrix.submatrix_mul_equiv, CFC.abs_mul_abs]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
  · exact ((CFC.abs_nonneg A).posSemidef.submatrix e).nonneg

omit [DecidableEq ι] [DecidableEq κ] in
/--
@isnad1 id=eq.0h4v.s6.678e8dbb083b from=translated src=- shape=f18495ff vocab=f5c0190d
-/
theorem trace_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)

/--
@isnad1 id=eq.0h4v.s6.c8e802a631d7 from=translated src=- shape=b0e006e1 vocab=d22abd06
-/
theorem traceNorm_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    traceNorm (A.submatrix e e) = traceNorm A := by
  rw [traceNorm, abs_submatrix_equiv, trace_submatrix_equiv]
  rfl

end Hellinger.TraceNorm
