import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TransformDomain.Transform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/SVD/FDiagonal.lean
  Definition 29 (f-diagonal tensor).

  A tensor is f-diagonal if all its frontal slices are diagonal matrices.
  Equivalently, this holds in the transform domain.
-/

namespace TubalTensor

open Matrix

variable {n : ℕ} {td : TubalData n} {m p : ℕ}

/-! ## Definition 29: f-diagonal tensor -/

/-- **Definition 29.** A tubal matrix is f-diagonal if all its frontal slices
    are diagonal matrices: for every i ≠ j, the (i,j) tube is zero.-/
def IsFDiagonal (A : TubalMatrix m p n td) : Prop :=
  ∀ (i : Fin m) (j : Fin p), (i : ℕ) ≠ (j : ℕ) → A i j = 0

/-- f-diagonal in primal domain implies diagonal frontal slices in the transform domain.
@isnad1 id=eq.2h8v.s5.c1f42ef5fe72 from=translated src=- shape=9cfff6bc vocab=48d57185
-/
theorem IsFDiagonal.transform_diag {A : TubalMatrix m p n td}
    (hA : IsFDiagonal A) (k : Fin n) (i : Fin m) (j : Fin p)
    (hij : (i : ℕ) ≠ (j : ℕ)) : transform A k i j = 0 := by
  simp [transform_apply, hA i j hij, KM.toFun_zero, toComplex_zero]

end TubalTensor
