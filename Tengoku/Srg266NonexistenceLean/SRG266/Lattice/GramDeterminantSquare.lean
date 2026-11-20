/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Matrix

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/--
@isnad1 id=eq.0h5v.s11.a4b0f49c3965 from=translated src=- shape=370d9efa vocab=3e39fa39
-/
theorem gram_rows_eq_mul (C : Matrix ι ι R) (v : Matrix κ ι R) :
    (fun i j => Matrix.toBilin' C (v i) (v j) : Matrix κ κ R) = v*C*v.transpose := by
  ext i j
  simp only [Matrix.toBilin'_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/--
@isnad1 id=ex.0h4v.s11.63fc63b2930d from=translated src=- shape=d8efbf10 vocab=64e238f8
-/
theorem gram_det_square (C : Matrix ι ι R) (v : Matrix ι ι R) :
    ∃ d : R, Matrix.det (fun i j => Matrix.toBilin' C (v i) (v j)) = C.det*d^2 := by
  refine ⟨v.det, ?_⟩
  rw [gram_rows_eq_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

end SRG266.Lattice
