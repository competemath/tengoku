/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.OrthogonalUnitary
import Tengoku.Seed.Analysis.Matrix.Spectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / NormalMatrix —— 正规、Hermitian 与斜 Hermitian 矩阵

本文件建立复方阵的正规、Hermitian 和斜 Hermitian 教材接口。每个复方阵都唯一地
分成 Hermitian 部分与斜 Hermitian 部分；两类矩阵都正规。最后给出 Hermitian 矩阵
的酉对角化，其特征值全部为实数。

> **Entry**: linear-algebra.matrix.hermitian
-/

namespace SandronesLibrary.LinearAlgebra.NormalMatrix

open scoped Matrix
open SandronesLibrary.LinearAlgebra.OrthogonalUnitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 正规矩阵：矩阵与其共轭转置可交换。-/
def IsNormalMatrix (A : Matrix n n ℂ) : Prop := Aᴴ * A = A * Aᴴ

/-- Hermitian 矩阵：共轭转置等于自身。-/
def IsHermitianMatrix (A : Matrix n n ℂ) : Prop := Aᴴ = A

/-- 斜 Hermitian 矩阵：共轭转置等于自身的负。-/
def IsSkewHermitianMatrix (A : Matrix n n ℂ) : Prop := Aᴴ = -A

/-- Hermitian 矩阵必为正规矩阵。-/
theorem hermitian_is_normal {A : Matrix n n ℂ}
    (hA : IsHermitianMatrix A) : IsNormalMatrix A := by
  simp only [IsHermitianMatrix] at hA
  simp [IsNormalMatrix, hA]

/-- 斜 Hermitian 矩阵必为正规矩阵。-/
theorem skewHermitian_is_normal {A : Matrix n n ℂ}
    (hA : IsSkewHermitianMatrix A) : IsNormalMatrix A := by
  simp only [IsSkewHermitianMatrix] at hA
  simp [IsNormalMatrix, hA]

/-- 矩阵的 Hermitian 部分 `(A+Aᴴ)/2`。-/
noncomputable def hermitianPart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)

/-- 矩阵的斜 Hermitian 部分 `(A-Aᴴ)/2`。-/
noncomputable def skewHermitianPart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (A - Aᴴ)

/-- Hermitian 部分确实是 Hermitian 矩阵。-/
theorem hermitianPart_isHermitian (A : Matrix n n ℂ) :
    IsHermitianMatrix (hermitianPart A) := by
  simp [IsHermitianMatrix, hermitianPart, Matrix.conjTranspose_add]
  module

/-- 斜 Hermitian 部分确实是斜 Hermitian 矩阵。-/
theorem skewHermitianPart_isSkewHermitian (A : Matrix n n ℂ) :
    IsSkewHermitianMatrix (skewHermitianPart A) := by
  simp [IsSkewHermitianMatrix, skewHermitianPart, Matrix.conjTranspose_sub]
  module

/-- 每个复方阵等于其 Hermitian 部分与斜 Hermitian 部分之和。-/
theorem hermitian_add_skewHermitian (A : Matrix n n ℂ) :
    hermitianPart A + skewHermitianPart A = A := by
  simp [hermitianPart, skewHermitianPart]
  module

/-- Hermitian 矩阵可由酉矩阵对角化，且所有对角元都是实数。-/
theorem hermitian_unitary_diagonalization {A : Matrix n n ℂ}
    (hA : IsHermitianMatrix A) :
    ∃ (U : Matrix n n ℂ) (μ : n → ℝ),
      IsUnitaryMatrix U ∧
        A = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
  have h : A.IsHermitian := hA
  let U := h.eigenvectorUnitary
  refine ⟨U, h.eigenvalues, ?_, ?_⟩
  · change (U : Matrix n n ℂ)ᴴ * U = 1
    simpa only [← Matrix.star_eq_conjTranspose] using U.property.1
  · change A = (U : Matrix n n ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) *
        (star U : Matrix n n ℂ)
    exact h.spectral_theorem

end SandronesLibrary.LinearAlgebra.NormalMatrix
