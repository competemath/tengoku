/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.LinearAlgebra.UnitaryGroup
import Tengoku.Seed.Analysis.CStarAlgebra.Matrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / OrthogonalUnitary —— 正交矩阵与酉矩阵

正交矩阵和酉矩阵分别保持实、复欧氏空间的内积。教材定义要求转置或共轭转置乘
自身等于单位矩阵；有限方阵情形下，另一侧乘积也自动等于单位矩阵，因此这些矩阵
组成群。本文建立教材谓词与 mathlib 矩阵群的桥，并记录乘法、共轭转置和行列式性质。

> **Entry**: linear-algebra.matrix.orthogonal-unitary
-/

namespace SandronesLibrary.LinearAlgebra.OrthogonalUnitary

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 复酉矩阵：共轭转置乘自身等于单位矩阵。-/
def IsUnitaryMatrix (A : Matrix n n ℂ) : Prop := Aᴴ * A = 1

/-- 实正交矩阵：转置乘自身等于单位矩阵。-/
def IsOrthogonalMatrix (A : Matrix n n ℝ) : Prop := Aᵀ * A = 1

/-- 教材酉矩阵谓词等价于属于酉群。-/
theorem isUnitaryMatrix_iff_mem (A : Matrix n n ℂ) :
    IsUnitaryMatrix A ↔ A ∈ Matrix.unitaryGroup n ℂ := by
  simpa [IsUnitaryMatrix, Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff' (A := A)).symm

/-- 教材正交矩阵谓词等价于属于正交群。-/
theorem isOrthogonalMatrix_iff_mem (A : Matrix n n ℝ) :
    IsOrthogonalMatrix A ↔ A ∈ Matrix.orthogonalGroup n ℝ := by
  simpa [IsOrthogonalMatrix] using
    (Matrix.mem_orthogonalGroup_iff' (A := A)).symm

/-- 两个酉矩阵的乘积仍为酉矩阵。-/
theorem unitary_mul {A B : Matrix n n ℂ}
    (hA : IsUnitaryMatrix A) (hB : IsUnitaryMatrix B) :
    IsUnitaryMatrix (A * B) := by
  rw [isUnitaryMatrix_iff_mem] at hA hB ⊢
  exact (Matrix.unitaryGroup n ℂ).mul_mem hA hB

/-- 酉矩阵的共轭转置仍为酉矩阵。-/
theorem unitary_conjTranspose {A : Matrix n n ℂ}
    (hA : IsUnitaryMatrix A) : IsUnitaryMatrix Aᴴ := by
  rw [isUnitaryMatrix_iff_mem] at hA ⊢
  simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hA

/-- 酉矩阵的行列式绝对值等于一。-/
theorem unitary_det_norm {A : Matrix n n ℂ}
    (hA : IsUnitaryMatrix A) : ‖A.det‖ = 1 := by
  apply CStarRing.norm_of_mem_unitary
  exact Matrix.det_of_mem_unitary ((isUnitaryMatrix_iff_mem A).mp hA)

/-- 实正交矩阵的行列式只能为 `1` 或 `-1`。-/
theorem orthogonal_det {A : Matrix n n ℝ}
    (hA : IsOrthogonalMatrix A) : A.det = 1 ∨ A.det = -1 := by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using!
    Matrix.det_of_mem_unitary ((isOrthogonalMatrix_iff_mem A).mp hA)

end SandronesLibrary.LinearAlgebra.OrthogonalUnitary
