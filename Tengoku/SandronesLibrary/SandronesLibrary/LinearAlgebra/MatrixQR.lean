/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.InnerProduct
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.OrthogonalUnitary
import Tengoku.Seed.Analysis.InnerProductSpace.GramSchmidtOrtho
import Tengoku.Seed.LinearAlgebra.Matrix.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / MatrixQR —— QR 分解

本文件从有限维实内积空间中的 Gram–Schmidt 正交化构造矩阵的 QR 分解。
即使输入矩阵奇异，mathlib 的正交基延拓也会补齐退化的正交化向量，因此仍能得到
一个方正交矩阵 `Q` 和上三角矩阵 `R`，使 `A = QR`。

> **Entry**: linear-algebra.decomposition.qr
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Matrix
open SandronesLibrary.LinearAlgebra.OrthogonalUnitary

/-- 实方阵的 QR 分解证书：`Q` 正交、`R` 上三角且 `A = QR`。-/
structure QRFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  orthogonal : Matrix (Fin n) (Fin n) ℝ
  upper : Matrix (Fin n) (Fin n) ℝ
  orthogonal_matrix : IsOrthogonalMatrix orthogonal
  upper_triangular : upper.IsUpperTriangular
  eq_mul : A = orthogonal * upper

/-- 把矩阵的列视为实欧氏空间中的向量族。-/
noncomputable def qrColumns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → EuclideanSpace ℝ (Fin n) :=
  fun j => WithLp.toLp 2 (Aᵀ j)

/-- 对矩阵列族进行 Gram–Schmidt，并在退化情形补齐为标准正交基。-/
noncomputable def qrBasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis finrank_euclideanSpace (qrColumns A)

/-- QR 分解中的正交因子；它的各列是 `qrBasis A`。-/
noncomputable def qrQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix (qrBasis A).toBasis

/-- QR 分解中的上三角因子；它记录原列向量在 `qrBasis A` 下的坐标。-/
noncomputable def qrR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (qrBasis A).toBasis.toMatrix (qrColumns A)

/-- Gram–Schmidt 所得基的坐标矩阵是正交矩阵。-/
theorem qrQ_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsOrthogonalMatrix (qrQ A) := by
  rw [qrQ, isOrthogonalMatrix_iff_mem]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal (qrBasis A)

/-- 原列向量在 Gram–Schmidt 基下的坐标矩阵为上三角矩阵。-/
theorem qrR_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (qrR A).IsUpperTriangular := by
  exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular
    finrank_euclideanSpace (qrColumns A)

/-- 两次换基矩阵相乘恢复原矩阵。-/
theorem qr_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    qrQ A * qrR A = A := by
  rw [qrQ, qrR, Module.Basis.toMatrix_mul_toMatrix]
  rfl

/-- 任意实方阵都存在方 QR 分解。-/
theorem exists_qr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Nonempty (QRFactorization A) := by
  exact ⟨{
    orthogonal := qrQ A
    upper := qrR A
    orthogonal_matrix := qrQ_orthogonal A
    upper_triangular := qrR_upper A
    eq_mul := (qr_mul A).symm }⟩

/-! ## 非奇异矩阵的正对角规范与唯一性 -/

/-- 非奇异实方阵的正对角规范 QR 分解。正对角条件消除了逐列改变符号造成的歧义。-/
structure PositiveQRFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    extends QRFactorization A where
  upper_diagonal_pos : ∀ i, 0 < upper i i

/-- 非零行列式保证矩阵的欧氏列族线性无关。-/
theorem qrColumns_linearIndependent_of_det_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    LinearIndependent ℝ (qrColumns A) := by
  have h := (A.linearIndependent_cols_of_det_ne_zero hA).map'
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.ker
  change LinearIndependent ℝ
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm ∘ Matrix.transpose A)
  exact h

/-- 规范化的第 `i` 个 Gram–Schmidt 向量与第 `i` 个原向量的内积，
等于未规范化残差的范数。-/
theorem inner_gramSchmidtNormed_input {n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin n))
    (hf : LinearIndependent ℝ f) (i : Fin n) :
    inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ f i) (f i) =
      ‖InnerProductSpace.gramSchmidt ℝ f i‖ := by
  let g := InnerProductSpace.gramSchmidt ℝ f i
  have hg : g ≠ 0 := InnerProductSpace.gramSchmidt_ne_zero i hf
  have hinner : inner ℝ g (f i) = ‖g‖ ^ 2 := by
    rw [InnerProductSpace.gramSchmidt_def'' ℝ f i, inner_add_right]
    rw [inner_sum]
    rw [real_inner_self_eq_norm_sq, add_eq_left]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_Iio] at hx
    rw [inner_smul_right]
    have horth : inner ℝ g (InnerProductSpace.gramSchmidt ℝ f x) = 0 := by
      dsimp only [g]
      exact InnerProductSpace.gramSchmidt_orthogonal ℝ f (ne_of_gt hx)
    rw [horth]
    simp
  rw [InnerProductSpace.gramSchmidtNormed, inner_smul_left, hinner]
  dsimp only [g] at hg ⊢
  rw [pow_two]
  exact inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hg) _

/-- 非奇异矩阵的 Gram–Schmidt 上三角因子具有严格正的对角元。-/
theorem qrR_diagonal_pos_of_det_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∀ i, 0 < qrR A i i := by
  intro i
  have hf : LinearIndependent ℝ (qrColumns A) :=
    qrColumns_linearIndependent_of_det_ne_zero A hA
  have hg : InnerProductSpace.gramSchmidt ℝ (qrColumns A) i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero i hf
  have hgn : InnerProductSpace.gramSchmidtNormed ℝ (qrColumns A) i ≠ 0 := by
    simp [InnerProductSpace.gramSchmidtNormed, hg]
  rw [qrR, Module.Basis.toMatrix_apply]
  rw [(qrBasis A).coe_toBasis_repr_apply, (qrBasis A).repr_apply_apply]
  rw [qrBasis, InnerProductSpace.gramSchmidtOrthonormalBasis_apply
    finrank_euclideanSpace hgn]
  rw [inner_gramSchmidtNormed_input (qrColumns A) hf i]
  exact norm_pos_iff.mpr hg

/-- 每个非奇异实方阵都存在正对角规范 QR 分解。-/
theorem exists_positive_qr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) : Nonempty (PositiveQRFactorization A) := by
  exact ⟨{
    orthogonal := qrQ A
    upper := qrR A
    orthogonal_matrix := qrQ_orthogonal A
    upper_triangular := qrR_upper A
    eq_mul := (qr_mul A).symm
    upper_diagonal_pos := qrR_diagonal_pos_of_det_ne_zero A hA }⟩

/-- 方正交矩阵的转置也是右逆。-/
theorem orthogonal_mul_transpose {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonalMatrix Q) : Q * Qᵀ = 1 := by
  have hmem := (isOrthogonalMatrix_iff_mem Q).mp hQ
  exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hmem

/-- 两个正交矩阵的交叉因子 `Q₁ᵀQ₂` 仍然正交。-/
theorem qr_cross_orthogonal {n : ℕ} {Q₁ Q₂ : Matrix (Fin n) (Fin n) ℝ}
    (hQ₁ : IsOrthogonalMatrix Q₁) (hQ₂ : IsOrthogonalMatrix Q₂) :
    IsOrthogonalMatrix (Q₁ᵀ * Q₂) := by
  unfold IsOrthogonalMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Q₁ Q₁ᵀ Q₂, orthogonal_mul_transpose hQ₁,
    Matrix.one_mul, hQ₂]

/-- 若右因子上三角，且左因子某行在 `j` 以前为零，则乘积的 `(i,j)` 元素
只剩两个对角位置元素的乘积。-/
theorem mul_apply_of_upper_of_left_prefix_zero {n : ℕ}
    (S R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hR : R.IsUpperTriangular) (hprev : ∀ k, k < j → S i k = 0) :
    (S * R) i j = S i j * R j j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single j
  · intro k _ hkj
    rcases lt_trichotomy k j with hlt | heq | hgt
    · rw [hprev k hlt, zero_mul]
    · exact (hkj heq).elim
    · have hz : R k j = 0 := by
        apply hR
        change j < k
        exact hgt
      rw [hz, mul_zero]
  · simp

/-- 若 `S R₂ = R₁`，两个 `R` 都上三角且 `R₂` 对角非零，则 `S` 也上三角。-/
theorem upper_left_factor_of_mul {n : ℕ}
    (S R₁ R₂ : Matrix (Fin n) (Fin n) ℝ)
    (hR₁ : R₁.IsUpperTriangular) (hR₂ : R₂.IsUpperTriangular)
    (hdR₂ : ∀ i, R₂ i i ≠ 0) (hmul : S * R₂ = R₁) :
    S.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  revert hij
  apply wellFounded_lt.induction j
  intro j ih hij
  have hprev : ∀ k, k < j → S i k = 0 := by
    intro k hkj
    exact ih k hkj (hkj.trans hij)
  have heq : S i j * R₂ j j = 0 := by
    rw [← mul_apply_of_upper_of_left_prefix_zero S R₂ i j hR₂ hprev]
    rw [hmul]
    apply hR₁
    change j < i
    exact hij
  exact (mul_eq_zero.mp heq).resolve_right (hdR₂ j)

/-- 在上一引理的三角情形中，若两个右侧因子的对角均为正，则左因子的对角也为正。-/
theorem upper_left_factor_diagonal_pos {n : ℕ}
    (S R₁ R₂ : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsUpperTriangular) (hR₂ : R₂.IsUpperTriangular)
    (hdR₁ : ∀ i, 0 < R₁ i i) (hdR₂ : ∀ i, 0 < R₂ i i)
    (hmul : S * R₂ = R₁) : ∀ i, 0 < S i i := by
  intro i
  have hprev : ∀ k, k < i → S i k = 0 := by
    intro k hki
    apply hS
    change k < i
    exact hki
  have heq : S i i * R₂ i i = R₁ i i := by
    rw [← mul_apply_of_upper_of_left_prefix_zero S R₂ i i hR₂ hprev, hmul]
  have hp : 0 < S i i * R₂ i i := heq.symm ▸ hdR₁ i
  rcases mul_pos_iff.mp hp with h | h
  · exact h.1
  · linarith [h.2, hdR₂ i]

/-- 正对角的上三角正交矩阵只能是单位矩阵。-/
theorem orthogonal_upper_pos_eq_one {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hSorth : IsOrthogonalMatrix S) (hSup : S.IsUpperTriangular)
    (hSpos : ∀ i, 0 < S i i) : S = 1 := by
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular := by
    intro i j hij
    simp only [Matrix.one_apply]
    exact ite_eq_right (by
      intro hji
      subst j
      exact lt_irrefl _ hij)
  have hSTup : Sᵀ.IsUpperTriangular :=
    upper_left_factor_of_mul Sᵀ 1 S hone hSup
      (fun i => ne_of_gt (hSpos i)) hSorth
  have hdiag : ∀ i, S i i = 1 := by
    intro i
    have hprev : ∀ k, k < i → Sᵀ i k = 0 := by
      intro k hki
      apply hSTup
      change k < i
      exact hki
    have heq := mul_apply_of_upper_of_left_prefix_zero Sᵀ S i i hSup hprev
    rw [hSorth] at heq
    simp only [Matrix.one_apply, ite_eq_left, Matrix.transpose_apply] at heq
    nlinarith [hSpos i]
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · have hz : Sᵀ j i = 0 := by
      apply hSTup
      change i < j
      exact hij
    simpa [Matrix.one_apply, ne_of_lt hij] using hz
  · subst j
    simp [hdiag]
  · have hz : S i j = 0 := by
      apply hSup
      change j < i
      exact hij
    simpa [Matrix.one_apply, ne_of_gt hij] using hz

/-- 非奇异实方阵的正对角规范 QR 分解唯一。-/
theorem positive_qr_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (fac₁ fac₂ : PositiveQRFactorization A) :
    fac₁.orthogonal = fac₂.orthogonal ∧ fac₁.upper = fac₂.upper := by
  let S := fac₁.orthogonalᵀ * fac₂.orthogonal
  have hcross : S * fac₂.upper = fac₁.upper := by
    calc
      S * fac₂.upper = fac₁.orthogonalᵀ *
          (fac₂.orthogonal * fac₂.upper) := Matrix.mul_assoc _ _ _
      _ = fac₁.orthogonalᵀ * A := congrArg _ fac₂.eq_mul.symm
      _ = fac₁.orthogonalᵀ *
          (fac₁.orthogonal * fac₁.upper) := congrArg _ fac₁.eq_mul
      _ = (fac₁.orthogonalᵀ * fac₁.orthogonal) * fac₁.upper :=
        (Matrix.mul_assoc _ _ _).symm
      _ = fac₁.upper := by rw [fac₁.orthogonal_matrix, Matrix.one_mul]
  have hSorth : IsOrthogonalMatrix S :=
    qr_cross_orthogonal fac₁.orthogonal_matrix fac₂.orthogonal_matrix
  have hSup : S.IsUpperTriangular :=
    upper_left_factor_of_mul S fac₁.upper fac₂.upper
      fac₁.upper_triangular fac₂.upper_triangular
      (fun i => ne_of_gt (fac₂.upper_diagonal_pos i)) hcross
  have hSpos : ∀ i, 0 < S i i :=
    upper_left_factor_diagonal_pos S fac₁.upper fac₂.upper hSup
      fac₂.upper_triangular fac₁.upper_diagonal_pos fac₂.upper_diagonal_pos hcross
  have hSone : S = 1 := orthogonal_upper_pos_eq_one S hSorth hSup hSpos
  have hQ : fac₁.orthogonal = fac₂.orthogonal := by
    calc
      fac₁.orthogonal = fac₁.orthogonal * 1 := (Matrix.mul_one _).symm
      _ = fac₁.orthogonal * S := congrArg (fac₁.orthogonal * ·) hSone.symm
      _ = fac₂.orthogonal := by
        dsimp only [S]
        rw [← Matrix.mul_assoc]
        have hleft : fac₁.orthogonal * fac₁.orthogonalᵀ = 1 :=
          orthogonal_mul_transpose fac₁.orthogonal_matrix
        rw [hleft, Matrix.one_mul]
  refine ⟨hQ, ?_⟩
  have hprod : fac₂.orthogonal * fac₁.upper =
      fac₂.orthogonal * fac₂.upper := by
    calc
      _ = fac₁.orthogonal * fac₁.upper := congrArg (· * fac₁.upper) hQ.symm
      _ = A := fac₁.eq_mul.symm
      _ = fac₂.orthogonal * fac₂.upper := fac₂.eq_mul
  have hcancel := congrArg (fun M => fac₂.orthogonalᵀ * M) hprod
  rw [← Matrix.mul_assoc, fac₂.orthogonal_matrix, Matrix.one_mul,
    ← Matrix.mul_assoc, fac₂.orthogonal_matrix, Matrix.one_mul] at hcancel
  exact hcancel

/-! ## 满列秩矩形矩阵的薄 QR 分解 -/

/-- 满列秩矩形矩阵的薄 QR 分解证书。`Q` 只有 `n` 列，列标准正交；
`R` 是正对角上三角方阵。-/
structure ThinQRFactorization {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) where
  orthogonalColumns : Matrix (Fin m) (Fin n) ℝ
  upper : Matrix (Fin n) (Fin n) ℝ
  columns_orthonormal : orthogonalColumnsᵀ * orthogonalColumns = 1
  upper_triangular : upper.IsUpperTriangular
  upper_diagonal_pos : ∀ i, 0 < upper i i
  eq_mul : A = orthogonalColumns * upper

/-- 把矩形矩阵的列视为 `ℝᵐ` 中的向量族。-/
noncomputable def thinQRColumns {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Fin n → EuclideanSpace ℝ (Fin m) :=
  fun j => WithLp.toLp 2 (Aᵀ j)

/-- 对矩形矩阵的列作规范化 Gram–Schmidt。-/
noncomputable def thinQRVectors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Fin n → EuclideanSpace ℝ (Fin m) :=
  InnerProductSpace.gramSchmidtNormed ℝ (thinQRColumns A)

/-- 薄 QR 的矩形正交列因子。-/
noncomputable def thinQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => thinQRVectors A j i

/-- 薄 QR 的上三角因子，由正交列与原列的内积给出。-/
noncomputable def thinR {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ (thinQRVectors A i) (thinQRColumns A j)

/-- 不同数量的向量与环境维数下，规范化 Gram–Schmidt 对角系数仍等于残差范数。-/
theorem inner_thin_gramSchmidtNormed_input {m n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin m))
    (hf : LinearIndependent ℝ f) (i : Fin n) :
    inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ f i) (f i) =
      ‖InnerProductSpace.gramSchmidt ℝ f i‖ := by
  let g := InnerProductSpace.gramSchmidt ℝ f i
  have hg : g ≠ 0 := InnerProductSpace.gramSchmidt_ne_zero i hf
  have hinner : inner ℝ g (f i) = ‖g‖ ^ 2 := by
    rw [InnerProductSpace.gramSchmidt_def'' ℝ f i, inner_add_right]
    rw [inner_sum]
    rw [real_inner_self_eq_norm_sq, add_eq_left]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_Iio] at hx
    rw [inner_smul_right]
    have horth : inner ℝ g (InnerProductSpace.gramSchmidt ℝ f x) = 0 := by
      dsimp only [g]
      exact InnerProductSpace.gramSchmidt_orthogonal ℝ f (ne_of_gt hx)
    rw [horth]
    simp
  rw [InnerProductSpace.gramSchmidtNormed, inner_smul_left, hinner]
  dsimp only [g] at hg ⊢
  rw [pow_two]
  exact inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hg) _

/-- 满列秩时，薄因子的列标准正交。-/
theorem thinQ_orthonormal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (thinQRColumns A)) :
    (thinQ A)ᵀ * thinQ A = 1 := by
  have hq : Orthonormal ℝ (thinQRVectors A) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal hA
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k, thinQRVectors A i k * thinQRVectors A j k) = _
  rw [show (∑ k, thinQRVectors A i k * thinQRVectors A j k) =
      inner ℝ (thinQRVectors A i) (thinQRVectors A j) by
    simp [PiLp.inner_apply, mul_comm]]
  simpa [Matrix.one_apply] using (orthonormal_iff_ite.mp hq i j)

/-- 满列秩时，薄 QR 的第二因子上三角且对角严格为正。-/
theorem thinR_upper_and_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (thinQRColumns A)) :
    (thinR A).IsUpperTriangular ∧ ∀ i, 0 < thinR A i i := by
  constructor
  · intro i j hij
    change j < i at hij
    rw [thinR, thinQRVectors, InnerProductSpace.gramSchmidtNormed,
      inner_smul_left]
    rw [InnerProductSpace.gramSchmidt_inv_triangular ℝ (thinQRColumns A) hij]
    simp
  · intro i
    rw [thinR, thinQRVectors]
    rw [inner_thin_gramSchmidtNormed_input (thinQRColumns A) hA i]
    exact norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero i hA)

/-- 线性无关向量族中，每个原向量都由规范化 Gram–Schmidt 族按其内积系数重构。-/
theorem gramSchmidtNormed_reconstruction {m n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin m))
    (hf : LinearIndependent ℝ f) (j : Fin n) :
    ∑ i, inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ f i) (f j) •
      InnerProductSpace.gramSchmidtNormed ℝ f i = f j := by
  let q := InnerProductSpace.gramSchmidtNormed ℝ f
  have hq : Orthonormal ℝ q :=
    InnerProductSpace.gramSchmidtNormed_orthonormal hf
  have hmem : f j ∈ Submodule.span ℝ (Set.range q) := by
    dsimp only [q]
    rw [InnerProductSpace.span_gramSchmidtNormed_range,
      InnerProductSpace.span_gramSchmidt]
    exact Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hci : ∀ i, c i = inner ℝ (q i) (f j) := by
    intro i
    calc
      c i = inner ℝ (q i) (∑ k, c k • q k) :=
        (hq.inner_right_fintype c i).symm
      _ = inner ℝ (q i) (f j) := congrArg (inner ℝ (q i)) hc
  calc
    ∑ i, inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ f i) (f j) •
        InnerProductSpace.gramSchmidtNormed ℝ f i =
        ∑ i, c i • q i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hci]
    _ = f j := hc

/-- 薄 QR 两个因子的乘积恢复原矩形矩阵。-/
theorem thinQR_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (thinQRColumns A)) :
    thinQ A * thinR A = A := by
  ext i j
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x i)
    (gramSchmidtNormed_reconstruction (thinQRColumns A) hA j)
  simpa [Matrix.mul_apply, thinQ, thinR, thinQRVectors, thinQRColumns,
    mul_comm] using h

/-- 任意满列秩实矩形矩阵都存在薄 QR 分解。列线性无关本身已经推出 `n ≤ m`，
因此无需另列尺寸不等式。-/
theorem exists_thin_qr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (thinQRColumns A)) :
    Nonempty (ThinQRFactorization A) := by
  obtain ⟨hup, hpos⟩ := thinR_upper_and_pos A hA
  exact ⟨{
    orthogonalColumns := thinQ A
    upper := thinR A
    columns_orthonormal := thinQ_orthonormal A hA
    upper_triangular := hup
    upper_diagonal_pos := hpos
    eq_mul := (thinQR_mul A hA).symm }⟩

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
