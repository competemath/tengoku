/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.MatrixQR
import Tengoku.Seed.Analysis.Matrix.LDL

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / MatrixCholesky —— Cholesky 分解

本文件利用 mathlib 的 LDL 分解构造实对称正定矩阵的 Cholesky 分解
\`A = LLᵀ\`。构造出的下三角因子具有严格正对角，并证明了这种规范化分解的唯一性。

> **Entry**: linear-algebra.decomposition.cholesky
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Matrix
open SandronesLibrary.LinearAlgebra.OrthogonalUnitary

/-- 实对称正定矩阵的 Cholesky 分解。-/
structure CholeskyFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  lower : Matrix (Fin n) (Fin n) ℝ
  lower_triangular : lower.IsLowerTriangular
  lower_diagonal_pos : ∀ i, 0 < lower i i
  eq_mul_transpose : A = lower * lowerᵀ

/--
@isnad1 id=and.1h2v.s6.730fe3e4aa36 from=translated src=- shape=30be89a8 vocab=ba83522c
-/
theorem LDL_lowerInv_unitLower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    (LDL.lowerInv hA).IsLowerTriangular ∧ ∀ i, LDL.lowerInv hA i i = 1 := by
  constructor
  · intro i j hij
    apply LDL.lowerInv_triangular hA
    change i < j at hij
    exact hij
  · intro i
    rw [LDL.lowerInv, InnerProductSpace.gramSchmidt_def]
    simp only [Pi.basisFun_apply, Pi.sub_apply, Finset.sum_apply]
    rw [Pi.single_eq_same, sub_eq_self]
    apply Finset.sum_eq_zero
    intro c hc
    rw [Submodule.starProjection_singleton]
    simp only [Pi.smul_apply]
    have hz := LDL.lowerInv_triangular hA (Finset.mem_Iio.mp hc)
    rw [LDL.lowerInv] at hz
    rw [hz]
    simp

/--
@isnad1 id=lt.1h3v.s5.379be0774e68 from=translated src=- shape=5a4363ce vocab=0f3125fa
-/
theorem LDL_diagEntries_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : ∀ i, 0 < LDL.diagEntries hA i := by
  intro i
  rw [LDL.diagEntries, EuclideanSpace.inner_toLp_toLp]
  rw [dotProduct_comm, star_star]
  apply hA.dotProduct_mulVec_pos
  intro hz
  have hii := congrFun hz i
  change LDL.lowerInv hA i i = 0 at hii
  rw [(LDL_lowerInv_unitLower hA).2 i] at hii
  exact one_ne_zero hii

/--
@isnad1 id=and.1h2v.s6.ec234dba33de from=translated src=- shape=30be89a8 vocab=226f1673
-/
theorem LDL_lower_unitLower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    (LDL.lower hA).IsLowerTriangular ∧ ∀ i, LDL.lower hA i i = 1 := by
  let N := LDL.lowerInv hA
  let L := LDL.lower hA
  let _ := LDL.invertibleLowerInv hA
  have hunit : IsUnit N.det := Matrix.isUnit_det_of_invertible N
  have hNlow : N.IsLowerTriangular := (LDL_lowerInv_unitLower hA).1
  have hNtup : Nᵀ.IsUpperTriangular := by
    intro i j hij
    apply hNlow
    exact hij
  have hNL : N * L = 1 := by
    dsimp only [N, L, LDL.lower]
    exact Matrix.mul_nonsing_inv _ hunit
  have hLtNt : Lᵀ * Nᵀ = 1 := by
    rw [← Matrix.transpose_mul, hNL, Matrix.transpose_one]
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular := by
    intro i j hij
    simp only [Matrix.one_apply]
    exact ite_eq_right (by
      intro hji
      subst j
      exact lt_irrefl _ hij)
  have hLtup : Lᵀ.IsUpperTriangular :=
    upper_left_factor_of_mul Lᵀ 1 Nᵀ hone hNtup
      (fun i => by simp [N, (LDL_lowerInv_unitLower hA).2 i]) hLtNt
  have hLlow : L.IsLowerTriangular := by
    intro i j hij
    apply hLtup
    exact hij
  refine ⟨hLlow, ?_⟩
  intro i
  have hprev : ∀ k, k < i → Lᵀ i k = 0 := by
    intro k hki
    apply hLtup
    change k < i
    exact hki
  have heq := mul_apply_of_upper_of_left_prefix_zero Lᵀ Nᵀ i i hNtup hprev
  rw [hLtNt] at heq
  simp only [Matrix.one_apply, ite_eq_left, Matrix.transpose_apply] at heq
  dsimp only [N, L] at heq
  rw [(LDL_lowerInv_unitLower hA).2 i, mul_one] at heq
  exact heq.symm

noncomputable def choleskyDiagonal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => Real.sqrt (LDL.diagEntries hA i)

noncomputable def choleskyLower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : Matrix (Fin n) (Fin n) ℝ :=
  LDL.lower hA * choleskyDiagonal hA

/--
@isnad1 id=eq.1h2v.s6.3e048b4b5950 from=translated src=- shape=3724f5e9 vocab=3d161559
-/
theorem choleskyDiagonal_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    choleskyDiagonal hA * choleskyDiagonal hA = LDL.diag hA := by
  rw [choleskyDiagonal, Matrix.diagonal_mul_diagonal, LDL.diag]
  congr 1
  funext i
  simpa [pow_two] using Real.sq_sqrt (le_of_lt (LDL_diagEntries_pos hA i))

/--
@isnad1 id=and.1h2v.s5.1f9eee8c8bf2 from=translated src=- shape=5ba05e6b vocab=073d1417
-/
theorem choleskyLower_properties {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    (choleskyLower hA).IsLowerTriangular ∧
      (∀ i, 0 < choleskyLower hA i i) := by
  have hL := LDL_lower_unitLower hA
  constructor
  · intro i j hij
    rw [choleskyLower, choleskyDiagonal, Matrix.mul_diagonal]
    rw [hL.1 hij, zero_mul]
  · intro i
    rw [choleskyLower, choleskyDiagonal, Matrix.mul_diagonal, hL.2 i, one_mul]
    exact Real.sqrt_pos.2 (LDL_diagEntries_pos hA i)

/--
@isnad1 id=eq.1h2v.s6.c2eee4f514c9 from=translated src=- shape=3d4eaf26 vocab=1335dbe4
-/
theorem choleskyLower_mul_transpose {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    choleskyLower hA * (choleskyLower hA)ᵀ = A := by
  rw [choleskyLower, Matrix.transpose_mul]
  have hDt : (choleskyDiagonal hA)ᵀ = choleskyDiagonal hA := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := fun h => hij h.symm
      simp [choleskyDiagonal, Matrix.transpose_apply, hij, hji]
  rw [hDt]
  calc
    (LDL.lower hA * choleskyDiagonal hA) *
        (choleskyDiagonal hA * (LDL.lower hA)ᵀ) =
        LDL.lower hA *
          (choleskyDiagonal hA * choleskyDiagonal hA) *
            (LDL.lower hA)ᵀ := by simp only [Matrix.mul_assoc]
    _ = LDL.lower hA * LDL.diag hA * (LDL.lower hA)ᵀ := by
      rw [choleskyDiagonal_sq hA]
    _ = A := LDL.lower_conj_diag hA

/--
@isnad1 id=nonempty.1h2v.s4.96011a8a9e81 from=translated src=- shape=c4d8f97a vocab=78e7c744
-/
theorem exists_cholesky {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) : Nonempty (CholeskyFactorization A) := by
  obtain ⟨hlow, hdiag⟩ := choleskyLower_properties hA
  exact ⟨{
    lower := choleskyLower hA
    lower_triangular := hlow
    lower_diagonal_pos := hdiag
    eq_mul_transpose := (choleskyLower_mul_transpose hA).symm }⟩

/--
@isnad1 id=ex.3h3v.s7.51d29eb307e2 from=translated src=- shape=0147acf2 vocab=2823228f
-/
theorem cholesky_cross_factor {n : ℕ}
    (L₁ L₂ : Matrix (Fin n) (Fin n) ℝ)
    (hL₁ : L₁.IsLowerTriangular) (hdL₁ : ∀ i, 0 < L₁ i i)
    (hprod : L₁ * L₁ᵀ = L₂ * L₂ᵀ) :
    ∃ S, IsOrthogonalMatrix S ∧ L₁ᵀ = S * L₂ᵀ := by
  have hdet : L₁.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L₁ hL₁]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hdL₁ i))
  have hunit : IsUnit L₁.det := isUnit_iff_ne_zero.mpr hdet
  let N := L₁⁻¹
  let S := N * L₂
  have hNL : N * L₁ = 1 := by
    dsimp only [N]
    exact Matrix.nonsing_inv_mul L₁ hunit
  have hLtNt : L₁ᵀ * Nᵀ = 1 := by
    rw [← Matrix.transpose_mul, hNL, Matrix.transpose_one]
  have hSR : S * L₂ᵀ = L₁ᵀ := by
    calc
      S * L₂ᵀ = N * (L₂ * L₂ᵀ) := Matrix.mul_assoc _ _ _
      _ = N * (L₁ * L₁ᵀ) := congrArg (N * ·) hprod.symm
      _ = (N * L₁) * L₁ᵀ := (Matrix.mul_assoc _ _ _).symm
      _ = L₁ᵀ := by rw [hNL, Matrix.one_mul]
  have hSright : S * Sᵀ = 1 := by
    dsimp only [S]
    rw [Matrix.transpose_mul]
    calc
      (N * L₂) * (L₂ᵀ * Nᵀ) = N * (L₂ * L₂ᵀ) * Nᵀ := by
        simp only [Matrix.mul_assoc]
      _ = N * (L₁ * L₁ᵀ) * Nᵀ := by rw [hprod]
      _ = (N * L₁) * (L₁ᵀ * Nᵀ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hNL, hLtNt, Matrix.mul_one]
  have hSorth : IsOrthogonalMatrix S := by
    rw [isOrthogonalMatrix_iff_mem]
    exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr hSright
  exact ⟨S, hSorth, hSR.symm⟩

/--
@isnad1 id=eq.0h4v.s5.ab7c30173d99 from=translated src=- shape=ab6671be vocab=b7aff0e8
-/
theorem cholesky_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (fac₁ fac₂ : CholeskyFactorization A) : fac₁.lower = fac₂.lower := by
  have hprod : fac₁.lower * fac₁.lowerᵀ = fac₂.lower * fac₂.lowerᵀ :=
    fac₁.eq_mul_transpose.symm.trans fac₂.eq_mul_transpose
  obtain ⟨S, hSorth, hSR⟩ := cholesky_cross_factor
    fac₁.lower fac₂.lower fac₁.lower_triangular
    fac₁.lower_diagonal_pos hprod
  have hR₁ : fac₁.lowerᵀ.IsUpperTriangular := by
    intro i j hij
    apply fac₁.lower_triangular
    exact hij
  have hR₂ : fac₂.lowerᵀ.IsUpperTriangular := by
    intro i j hij
    apply fac₂.lower_triangular
    exact hij
  let q₁ : PositiveQRFactorization fac₁.lowerᵀ := {
    orthogonal := 1
    upper := fac₁.lowerᵀ
    orthogonal_matrix := by simp [IsOrthogonalMatrix]
    upper_triangular := hR₁
    eq_mul := by simp
    upper_diagonal_pos := by
      intro i
      simpa using fac₁.lower_diagonal_pos i }
  let q₂ : PositiveQRFactorization fac₁.lowerᵀ := {
    orthogonal := S
    upper := fac₂.lowerᵀ
    orthogonal_matrix := hSorth
    upper_triangular := hR₂
    eq_mul := hSR
    upper_diagonal_pos := by
      intro i
      simpa using fac₂.lower_diagonal_pos i }
  have hR := (positive_qr_unique q₁ q₂).2
  apply Matrix.transpose_injective
  exact hR

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
