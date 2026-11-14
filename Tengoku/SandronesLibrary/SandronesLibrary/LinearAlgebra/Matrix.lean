/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 对称矩阵与反对称矩阵

本模块补齐线性代数教材中的两类基本方阵。方阵 `A` 若满足 `Aᵀ=A`，称为对称矩阵；
若满足 `Aᵀ=-A`，称为反对称矩阵或斜对称矩阵。前者逐元素满足 `aᵢⱼ=aⱼᵢ`，后者
满足 `aᵢⱼ=-aⱼᵢ`。

在特征零域上，反对称矩阵的主对角元全为零。更重要的是，每个方阵都有标准分解

`A = (A+Aᵀ)/2 + (A-Aᵀ)/2`，

其中第一项对称、第二项反对称。该分解是 Hessian、二次型、正交群李代数和谱定理
之间的基础接口。
-/

namespace SandronesLibrary.LinearAlgebra.Matrix

/-- **对称矩阵**：方阵的转置等于自身。-/
def IsSymmetric {n R : Type*} (A : Matrix n n R) : Prop := A.transpose = A

/-- **反对称矩阵（斜对称矩阵）**：方阵的转置等于自身的负矩阵。-/
def IsSkewSymmetric {n R : Type*} [Neg R] (A : Matrix n n R) : Prop :=
  A.transpose = -A

/-- 对称矩阵的逐元素判据：关于主对角线镜像的两个元素相等。

> **Entry**: linear-algebra.matrix.symmetric-/
theorem isSymmetric_iff_entries {n R : Type*} {A : Matrix n n R} :
    IsSymmetric A ↔ ∀ i j, A i j = A j i := by
  constructor
  · intro h i j
    have hij := congrFun (congrFun h j) i
    simpa [Matrix.transpose_apply] using hij
  · intro h
    ext i j
    exact h j i

/-- 本库教材定义与 Mathlib 的 `Matrix.IsSymm` 完全等价。-/
theorem isSymmetric_iff_mathlib {n R : Type*} {A : Matrix n n R} :
    IsSymmetric A ↔ A.IsSymm := by
  rfl

/-- 反对称矩阵的逐元素判据：`aᵢⱼ=-aⱼᵢ`。

> **Entry**: linear-algebra.matrix.skew-symmetric-/
theorem isSkewSymmetric_iff_entries {n R : Type*} [AddGroup R] {A : Matrix n n R} :
    IsSkewSymmetric A ↔ ∀ i j, A i j = -A j i := by
  constructor
  · intro h i j
    have hij := congrFun (congrFun h j) i
    simpa [Matrix.transpose_apply] using hij
  · intro h
    ext i j
    simpa using h j i

/-- 两个对称矩阵的和仍是对称矩阵。-/
theorem isSymmetric_add {n R : Type*} [Add R] {A B : Matrix n n R}
    (hA : IsSymmetric A) (hB : IsSymmetric B) : IsSymmetric (A + B) := by
  rw [IsSymmetric, Matrix.transpose_add, hA, hB]

/-- 两个反对称矩阵的和仍是反对称矩阵。-/
theorem isSkewSymmetric_add {n R : Type*} [AddCommGroup R] {A B : Matrix n n R}
    (hA : IsSkewSymmetric A) (hB : IsSkewSymmetric B) : IsSkewSymmetric (A + B) := by
  rw [IsSkewSymmetric, Matrix.transpose_add, hA, hB, neg_add_rev]
  exact add_comm _ _

/-- 在特征零域上，反对称矩阵的每个主对角元都等于零。证明使用
`aᵢᵢ=-aᵢᵢ`，从而 `2aᵢᵢ=0`。-/
theorem isSkewSymmetric_diagonal_eq_zero {n K : Type*} [Field K] [CharZero K]
    {A : Matrix n n K} (hA : IsSkewSymmetric A) (i : n) : A i i = 0 := by
  have hii : A i i = -A i i := (isSkewSymmetric_iff_entries.mp hA) i i
  have htwo : (2 : K) * A i i = 0 := by
    calc
      (2 : K) * A i i = A i i + A i i := two_mul _
      _ = -A i i + A i i := congrArg (fun z ↦ z + A i i) hii
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- 方阵的**对称部分** `(A+Aᵀ)/2`。-/
noncomputable def symmetricPart {n K : Type*} [Field K] (A : Matrix n n K) : Matrix n n K :=
  (2 : K)⁻¹ • (A + A.transpose)

/-- 方阵的**反对称部分** `(A-Aᵀ)/2`。-/
noncomputable def skewSymmetricPart {n K : Type*} [Field K]
    (A : Matrix n n K) : Matrix n n K :=
  (2 : K)⁻¹ • (A - A.transpose)

/-- `(A+Aᵀ)/2` 确实是对称矩阵。-/
theorem symmetricPart_isSymmetric {n K : Type*} [Field K] (A : Matrix n n K) :
    IsSymmetric (symmetricPart A) := by
  rw [isSymmetric_iff_entries]
  intro i j
  simp [symmetricPart, add_comm]

/-- `(A-Aᵀ)/2` 确实是反对称矩阵。-/
theorem skewSymmetricPart_isSkewSymmetric {n K : Type*} [Field K]
    (A : Matrix n n K) : IsSkewSymmetric (skewSymmetricPart A) := by
  rw [isSkewSymmetric_iff_entries]
  intro i j
  simp [skewSymmetricPart]
  ring

/-- **对称—反对称分解**：特征零域上的任意方阵都等于其对称部分与反对称部分之和。-/
theorem symmetricPart_add_skewSymmetricPart {n K : Type*} [Field K] [CharZero K]
    (A : Matrix n n K) : symmetricPart A + skewSymmetricPart A = A := by
  ext i j
  simp [symmetricPart, skewSymmetricPart]
  field_simp
  ring

end SandronesLibrary.LinearAlgebra.Matrix
