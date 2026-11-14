/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.LinearAlgebra.SymplecticGroup
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 辛矩阵框架

以 `J = [[0,-I],[I,0]]` 为标准辛矩阵，并采用教材条件 `Aᵀ J A = J`。

> **Entry**: linear-algebra.matrix.symplectic
-/

namespace SandronesLibrary.LinearAlgebra.SymplecticMatrix

open Matrix

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- 标准辛矩阵 `J = [[0,-I],[I,0]]`。-/
def standardJ : Matrix (l ⊕ l) (l ⊕ l) ℝ := Matrix.J l ℝ

/-- 辛矩阵的教材定义：`Aᵀ J A = J`。-/
def IsSymplecticMatrix (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop :=
  Aᵀ * standardJ * A = standardJ

/-- 教材定义与 mathlib 辛群成员条件一致。-/
theorem isSymplecticMatrix_iff_mem {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} :
    IsSymplecticMatrix A ↔ A ∈ Matrix.symplecticGroup l ℝ := by
  simpa [IsSymplecticMatrix, standardJ] using
    (SymplecticGroup.mem_iff' (l := l) (R := ℝ) (A := A)).symm

/-- 标准辛矩阵是斜对称矩阵。-/
theorem standardJ_transpose : (standardJ : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ = -standardJ := by
  exact Matrix.J_transpose l ℝ

/-- 标准辛矩阵满足 `J²=-I`。-/
theorem standardJ_sq :
    (standardJ : Matrix (l ⊕ l) (l ⊕ l) ℝ) * standardJ = -1 := by
  exact Matrix.J_squared l ℝ

/-- 单位矩阵是辛矩阵。-/
theorem one_isSymplectic :
    IsSymplecticMatrix (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
  rw [isSymplecticMatrix_iff_mem]
  exact (Matrix.symplecticGroup l ℝ).one_mem

/-- 两个辛矩阵的乘积仍是辛矩阵。-/
theorem mul_isSymplectic {A B : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : IsSymplecticMatrix A) (hB : IsSymplecticMatrix B) :
    IsSymplecticMatrix (A * B) := by
  rw [isSymplecticMatrix_iff_mem] at hA hB ⊢
  exact (Matrix.symplecticGroup l ℝ).mul_mem hA hB

/-- 辛矩阵的辛逆矩阵公式 `A⁻¹=-J Aᵀ J`。-/
theorem inverse_formula {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : IsSymplecticMatrix A) :
    A⁻¹ = (-standardJ) * Aᵀ * standardJ := by
  apply SymplecticGroup.inv_eq_symplectic_inv
  exact isSymplecticMatrix_iff_mem.mp hA

/-- 辛矩阵的逆仍是辛矩阵。-/
theorem inv_isSymplectic {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : IsSymplecticMatrix A) : IsSymplecticMatrix A⁻¹ := by
  rw [isSymplecticMatrix_iff_mem]
  rw [inverse_formula hA]
  exact (Matrix.symplecticGroup l ℝ).mul_mem
    ((Matrix.symplecticGroup l ℝ).mul_mem
      (SymplecticGroup.neg_mem (SymplecticGroup.J_mem l ℝ))
      (SymplecticGroup.transpose_mem (isSymplecticMatrix_iff_mem.mp hA)))
    (SymplecticGroup.J_mem l ℝ)

/-- 实辛矩阵的行列式等于 `1`。-/
theorem det_eq_one {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : IsSymplecticMatrix A) : Matrix.det A = 1 := by
  exact SymplecticGroup.det_eq_one (isSymplecticMatrix_iff_mem.mp hA)

end SandronesLibrary.LinearAlgebra.SymplecticMatrix
