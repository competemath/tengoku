/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.MatrixElimination
import Tengoku.Seed.LinearAlgebra.Matrix.Permutation
import Tengoku.Seed.LinearAlgebra.Matrix.SchurComplement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LU 与 LDU 分解

本文件从教材中的分块高斯消元开始构造矩阵分解。若左上主元块 `A` 可逆，则
块矩阵可分解为单位下三角块、块对角矩阵和单位上三角块的乘积；中间右下块
`D - C A⁻¹ B` 是 `A` 的 Schur 补。

这个恒等式是无换行 LU/LDU 分解的递归步骤。一般 PLU 分解还需在每一步主元
不可逆时先交换行，后续将在本文件中接着构造。

> **Entry**: linear-algebra.decomposition.lu
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Matrix
open scoped Matrix

variable {K : Type*} [Field K]

/-- `A = LDU` 的数据证书。三角性条件由具体构造的定理另外给出，以便该结构也能
用于分块矩阵与其他索引类型。-/
structure LDUFactorization {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) where
  lower : Matrix n n K
  diagonal : Matrix n n K
  upper : Matrix n n K
  eq_mul : A = lower * diagonal * upper

/-- `A = LU` 的数据证书。-/
structure LUFactorization {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) where
  lower : Matrix n n K
  upper : Matrix n n K
  eq_mul : A = lower * upper

/-- `PA = LU` 的置换 LU 证书；下三角因子按标准方式规范化为单位对角。-/
structure PLUFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) K) where
  permutation : Equiv.Perm (Fin n)
  lower : Matrix (Fin n) (Fin n) K
  upper : Matrix (Fin n) (Fin n) K
  lower_triangular : lower.IsLowerTriangular
  upper_triangular : upper.IsUpperTriangular
  lower_diagonal_one : ∀ i, lower i i = 1
  eq_mul : permutation.permMatrix K * A = lower * upper

/-- 零阶矩阵的 PLU 证书，是递归构造的起点。-/
def pluZero : PLUFactorization (0 : Matrix (Fin 0) (Fin 0) K) where
  permutation := Equiv.refl _
  lower := 1
  upper := 1
  lower_triangular := by intro i; exact Fin.elim0 i
  upper_triangular := by intro i; exact Fin.elim0 i
  lower_diagonal_one := by intro i; exact Fin.elim0 i
  eq_mul := by ext i; exact Fin.elim0 i

/-- 可逆非空方阵的首列必含非零元，因而可以选取首个消元主元。
@isnad1 id=ex.1h3v.s7.9a5b25d75377 from=translated src=- shape=819b7c3f vocab=4d5f7101
-/
theorem firstColumn_nonzero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA : IsUnit A.det) : ∃ i, A i 0 ≠ 0 := by
  by_contra h
  push Not at h
  exact hA.ne_zero (Matrix.det_eq_zero_of_column_eq_zero 0 h)

/-- 交换第零行与第 `i` 行后，新的左上元正是原矩阵中选定的主元。
@isnad1 id=eq.0h4v.s8.9016bca0ea23 from=translated src=- shape=ece552db vocab=7b399633
-/
theorem pivotPermutation_entry {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin (n + 1)) :
    ((Equiv.swap 0 i).permMatrix K * A) 0 0 = A i 0 := by
  change (Matrix.swap K 0 i * A) 0 0 = A i 0
  exact Matrix.swap_mul_apply_left 0 i 0 A

/-- 置换行不改变可逆性。
@isnad1 id=isunit.1h4v.s8.1f5e62d7d4c4 from=translated src=- shape=3b349972 vocab=2210fc1c
-/
theorem pivotPermutation_isUnit_det {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hA : IsUnit A.det)
    (i : Fin (n + 1)) :
    IsUnit (((Equiv.swap 0 i).permMatrix K * A).det) := by
  rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.det_permute]
  exact (isUnit_iff_ne_zero.mpr (by
    by_cases h : (0 : Fin (n + 1)) = i <;> simp [h])).mul hA

/-- 把首个坐标与剩余坐标分开的标准等价。-/
def headTailEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  (finSumFinEquiv : Fin 1 ⊕ Fin n ≃ Fin (1 + n)).trans (finCongr (Nat.add_comm 1 n))

/--
@isnad1 id=eq.0h1v.s7.0b07857840ff from=translated src=- shape=f4dd044c vocab=0b5c7f76
-/
@[simp] theorem headTailEquiv_inl_zero (n : ℕ) :
    headTailEquiv n (Sum.inl 0) = 0 := by
  rfl

/--
@isnad1 id=eq.0h2v.s7.c6089c480ef7 from=translated src=- shape=71b0ecfe vocab=21e3a687
-/
@[simp] theorem headTailEquiv_inr (n : ℕ) (i : Fin n) :
    headTailEquiv n (Sum.inr i) = i.succ := by
  apply Fin.ext
  simp [headTailEquiv, finSumFinEquiv_apply_right]

/--
@isnad1 id=eq.0h1v.s7.6ab4fd707213 from=translated src=- shape=85161d95 vocab=f714956f
-/
@[simp] theorem headTailEquiv_symm_zero (n : ℕ) :
    (headTailEquiv n).symm 0 = Sum.inl 0 := by
  apply (headTailEquiv n).injective
  simp

/--
@isnad1 id=eq.0h2v.s7.fedb1d77cfc1 from=translated src=- shape=b71256f0 vocab=a1cd165a
-/
@[simp] theorem headTailEquiv_symm_succ (n : ℕ) (i : Fin n) :
    (headTailEquiv n).symm i.succ = Sum.inr i := by
  apply (headTailEquiv n).injective
  simp

/-- 方阵在首个坐标上的 `1 × 1` 主元块。-/
def leadingBlock {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin 1) (Fin 1) K :=
  fun i j => S (headTailEquiv n (Sum.inl i)) (headTailEquiv n (Sum.inl j))

/--
@isnad1 id=eq.0h3v.s7.8fa1a1fed532 from=translated src=- shape=999c4b0f vocab=994abd1b
-/
@[simp] theorem leadingBlock_entry {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : leadingBlock S 0 0 = S 0 0 := rfl

/-- 非零标量主元给出可逆的 `1 × 1` 主元块。
@isnad1 id=isunit.1h3v.s7.fc32a89d31c5 from=translated src=- shape=5cf7d02f vocab=b54e6236
-/
theorem leadingBlock_isUnit_det {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (h : S 0 0 ≠ 0) :
    IsUnit (leadingBlock S).det := by
  rw [Matrix.det_fin_one]
  exact isUnit_iff_ne_zero.mpr h

/-- 若整个块矩阵可逆且左上块可逆，则对应 Schur 补也可逆。
@isnad1 id=isunit.1h7v.s8.d8f9e8b5c9d8 from=translated src=- shape=d6e55ba2 vocab=aa1bca31
-/
theorem schurComplement_isUnit_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    [Invertible A] (hM : IsUnit (Matrix.fromBlocks A B C D).det) :
    IsUnit (D - C * ⅟A * B).det := by
  rw [Matrix.det_fromBlocks₁₁] at hM
  apply isUnit_iff_ne_zero.mpr
  intro h
  exact hM.ne_zero (by rw [h, mul_zero])

/-- 首行去掉首元后的右上块。-/
def topRightBlock {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin 1) (Fin n) K := fun i j => S (headTailEquiv n (Sum.inl i)) j.succ

/-- 首列去掉首元后的左下块。-/
def bottomLeftBlock {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin 1) K := fun i j => S i.succ (headTailEquiv n (Sum.inl j))

/-- 删去首行首列后的右下子矩阵。-/
def trailingBlock {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin n) K := fun i j => S i.succ j.succ

/-- 首坐标—剩余坐标重索引与四块矩阵表示完全一致。
@isnad1 id=eq.0h3v.s8.069988f1377a from=translated src=- shape=151a3bda vocab=4c075ff1
-/
theorem reindex_eq_fromBlocks {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    S.submatrix (headTailEquiv n) (headTailEquiv n) =
      Matrix.fromBlocks (leadingBlock S) (topRightBlock S)
        (bottomLeftBlock S) (trailingBlock S) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => rfl
      | inr j => simp [topRightBlock]
  | inr i =>
      cases j with
      | inl j => simp [bottomLeftBlock]
      | inr j => simp [trailingBlock]

/-- 一次完整的选主元步：可逆方阵可经一次换行得到可逆的
`1 × 1` 主元块，且消元后的 Schur 补仍可逆，因此可对其递归。
@isnad1 id=ex.1h3v.s9.b2469456e602 from=translated src=- shape=67eec587 vocab=124ddf86
-/
theorem pivotStep_schur_isUnit {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hA : IsUnit A.det) :
    ∃ i : Fin (n + 1),
      let S := (Equiv.swap 0 i).permMatrix K * A
      let A₁₁ := leadingBlock S
      A i 0 ≠ 0 ∧ IsUnit A₁₁.det ∧
        IsUnit (trailingBlock S - bottomLeftBlock S * A₁₁⁻¹ * topRightBlock S).det := by
  obtain ⟨i, hi⟩ := firstColumn_nonzero A hA
  refine ⟨i, hi, ?_, ?_⟩
  · exact leadingBlock_isUnit_det _ (pivotPermutation_entry A i |>.trans_ne hi)
  · let S := (Equiv.swap 0 i).permMatrix K * A
    have hlead : IsUnit (leadingBlock S).det :=
      leadingBlock_isUnit_det _ (pivotPermutation_entry A i |>.trans_ne hi)
    letI := Matrix.invertibleOfIsUnitDet (leadingBlock S) hlead
    rw [← Matrix.invOf_eq_nonsing_inv]
    apply schurComplement_isUnit_det
    rw [← reindex_eq_fromBlocks]
    rw [Matrix.det_submatrix_equiv_self]
    exact pivotPermutation_isUnit_det A hA i

/-- 把 `n × n` 矩阵嵌入右下角，并在左上角补一。-/
def liftTrailing {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks 1 0 0 M)

/--
@isnad1 id=eq.0h3v.s6.b93b20fffaaa from=translated src=- shape=864ac9d2 vocab=a76054ac
-/
@[simp] theorem liftTrailing_zero_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    liftTrailing M 0 0 = 1 := by
  simp [liftTrailing, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/--
@isnad1 id=eq.0h4v.s6.0e076df67525 from=translated src=- shape=52e2e015 vocab=858d409e
-/
@[simp] theorem liftTrailing_zero_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (j : Fin n) : liftTrailing M 0 j.succ = 0 := by
  simp [liftTrailing, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/--
@isnad1 id=eq.0h4v.s6.006c56c35094 from=translated src=- shape=10ea32eb vocab=858d409e
-/
@[simp] theorem liftTrailing_succ_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (i : Fin n) : liftTrailing M i.succ 0 = 0 := by
  simp [liftTrailing, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/--
@isnad1 id=eq.0h5v.s5.dbe9434e0a64 from=translated src=- shape=d6745427 vocab=6d9ead89
-/
@[simp] theorem liftTrailing_succ_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : liftTrailing M i.succ j.succ = M i j := by
  simp [liftTrailing, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/-- 右下嵌入保持乘法。
@isnad1 id=eq.0h4v.s8.65beeb6b95d3 from=translated src=- shape=8fefc014 vocab=30f33a1b
-/
theorem liftTrailing_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) K) :
    liftTrailing (M * N) = liftTrailing M * liftTrailing N := by
  rw [liftTrailing, liftTrailing, liftTrailing, ← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

/--
@isnad1 id=islowert.1h3v.s6.e0e6e635d1dd from=translated src=- shape=abe6e749 vocab=571544a5
-/
theorem liftTrailing_lower {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : M.IsLowerTriangular) : (liftTrailing M).IsLowerTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => exact liftTrailing_zero_succ M j
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          change i.succ < 0 at hij
          exact (Fin.not_lt_zero _ hij).elim
      | succ j =>
          rw [liftTrailing_succ_succ]
          exact hM (Fin.succ_lt_succ_iff.mp hij)

/--
@isnad1 id=isuppert.1h3v.s6.3c687637a2a0 from=translated src=- shape=abe6e749 vocab=0fa55bdf
-/
theorem liftTrailing_upper {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : M.IsUpperTriangular) : (liftTrailing M).IsUpperTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero => simp at hij
  | succ i =>
      cases j using Fin.cases with
      | zero => exact liftTrailing_succ_zero M i
      | succ j =>
          rw [liftTrailing_succ_succ]
          exact hM (Fin.succ_lt_succ_iff.mp hij)

/--
@isnad1 id=eq.1h4v.s6.0a8e41976285 from=translated src=- shape=0ca9c373 vocab=a76054ac
-/
theorem liftTrailing_diag_one {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i, M i i = 1) : ∀ i, liftTrailing M i i = 1 := by
  intro i
  cases i using Fin.cases with
  | zero => exact liftTrailing_zero_zero M
  | succ i => simpa using hM i

/-- 固定首坐标，并在其余坐标上作置换。-/
def liftPermutation {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (headTailEquiv n).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 1)) p).trans (headTailEquiv n))

/--
@isnad1 id=eq.0h2v.s7.3cb499ab59f9 from=translated src=- shape=c9c1a9cd vocab=a2ddf2a6
-/
@[simp] theorem liftPermutation_zero {n : ℕ} (p : Equiv.Perm (Fin n)) :
    liftPermutation p 0 = 0 := by
  simp [liftPermutation]

/--
@isnad1 id=eq.0h3v.s7.d7330a92fec5 from=translated src=- shape=bb4e08c5 vocab=3a7ea35e
-/
@[simp] theorem liftPermutation_succ {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    liftPermutation p i.succ = (p i).succ := by
  simp [liftPermutation]

/-- 置换的函数提升与置换矩阵的右下嵌入一致。
@isnad1 id=eq.0h3v.s7.f6251a1d556d from=translated src=- shape=3b5dd70c vocab=5d224749
-/
theorem liftPermutation_permMatrix {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (liftPermutation p).permMatrix K = liftTrailing (p.permMatrix K) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp [Equiv.Perm.permMatrix, PEquiv.toMatrix]
      | succ j =>
          simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, (Fin.succ_ne_zero j).symm]
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [Equiv.Perm.permMatrix, PEquiv.toMatrix]
      | succ j => simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, liftPermutation]

/-- 组装递归 PLU 的单位下三角因子。-/
def assembleLower {n : ℕ} (M : Matrix (Fin n) (Fin 1) K)
    (L : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks 1 0 M L)

/-- 组装递归 PLU 的上三角因子。-/
def assembleUpper {n : ℕ} (a : Matrix (Fin 1) (Fin 1) K)
    (B : Matrix (Fin 1) (Fin n) K) (U : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks a B 0 U)

/--
@isnad1 id=eq.0h6v.s5.36e5f8a406bd from=translated src=- shape=ddd52a8b vocab=b4d062b5
-/
@[simp] theorem assembleLower_succ_succ {n : ℕ} (M : Matrix (Fin n) (Fin 1) K)
    (L : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    assembleLower M L i.succ j.succ = L i j := by
  simp [assembleLower, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/--
@isnad1 id=eq.0h7v.s6.5f130392f733 from=translated src=- shape=ab85cde4 vocab=66a21bc7
-/
@[simp] theorem assembleUpper_succ_succ {n : ℕ} (a : Matrix (Fin 1) (Fin 1) K)
    (B : Matrix (Fin 1) (Fin n) K) (U : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    assembleUpper a B U i.succ j.succ = U i j := by
  simp [assembleUpper, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/--
@isnad1 id=islowert.1h4v.s6.9d2642712988 from=translated src=- shape=95656b13 vocab=5f9c9b34
-/
theorem assembleLower_lower {n : ℕ} (M : Matrix (Fin n) (Fin 1) K)
    {L : Matrix (Fin n) (Fin n) K} (hL : L.IsLowerTriangular) :
    (assembleLower M L).IsLowerTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => simp [assembleLower, Matrix.reindexAlgEquiv, Matrix.reindex_apply]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          change i.succ < 0 at hij
          exact (Fin.not_lt_zero _ hij).elim
      | succ j =>
          rw [assembleLower_succ_succ]
          exact hL (Fin.succ_lt_succ_iff.mp hij)

/--
@isnad1 id=eq.1h5v.s6.d8f7708c96c5 from=translated src=- shape=0dc42112 vocab=52e4fb08
-/
theorem assembleLower_diag_one {n : ℕ} (M : Matrix (Fin n) (Fin 1) K)
    {L : Matrix (Fin n) (Fin n) K} (hL : ∀ i, L i i = 1) :
    ∀ i, assembleLower M L i i = 1 := by
  intro i
  cases i using Fin.cases with
  | zero => simp [assembleLower, Matrix.reindexAlgEquiv, Matrix.reindex_apply]
  | succ i =>
      simpa [assembleLower, Matrix.reindexAlgEquiv, Matrix.reindex_apply] using hL i

/--
@isnad1 id=isuppert.1h5v.s6.96be87335bf1 from=translated src=- shape=9fb5568e vocab=004ad834
-/
theorem assembleUpper_upper {n : ℕ} (a : Matrix (Fin 1) (Fin 1) K)
    (B : Matrix (Fin 1) (Fin n) K) {U : Matrix (Fin n) (Fin n) K}
    (hU : U.IsUpperTriangular) : (assembleUpper a B U).IsUpperTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero => simp at hij
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [assembleUpper, Matrix.reindexAlgEquiv, Matrix.reindex_apply]
      | succ j =>
          rw [assembleUpper_succ_succ]
          exact hU (Fin.succ_lt_succ_iff.mp hij)

/--
@isnad1 id=eq.0h5v.s7.46ed022dcaba from=translated src=- shape=0c1e5b8b vocab=e78df0db
-/
@[simp] theorem assembleUpper_zero_zero {n : ℕ} (a : Matrix (Fin 1) (Fin 1) K)
    (B : Matrix (Fin 1) (Fin n) K) (U : Matrix (Fin n) (Fin n) K) :
    assembleUpper a B U 0 0 = a 0 0 := by
  simp [assembleUpper, Matrix.reindexAlgEquiv, Matrix.reindex_apply]

/-- 组装上三角块时，首主元和递归对角均非零则整个对角非零。
@isnad1 id=ne.2h6v.s7.90dbe048d61d from=translated src=- shape=17f808c9 vocab=e78df0db
-/
theorem assembleUpper_diag_ne_zero {n : ℕ} (a : Matrix (Fin 1) (Fin 1) K)
    (B : Matrix (Fin 1) (Fin n) K) {U : Matrix (Fin n) (Fin n) K}
    (ha : a 0 0 ≠ 0) (hU : ∀ i, U i i ≠ 0) :
    ∀ i, assembleUpper a B U i i ≠ 0 := by
  intro i
  cases i using Fin.cases with
  | zero => simpa using ha
  | succ i => simpa using hU i

/-- 若 Schur 补已有 `P'Q=L'U'`，则块乘法给出整个矩阵的递归乘积等式。
@isnad1 id=eq.1h9v.s11.6c96b7c226d5 from=translated src=- shape=7f8b7dc3 vocab=22bd6a57
-/
theorem recursive_block_product {n : ℕ}
    (a : Matrix (Fin 1) (Fin 1) K) (B : Matrix (Fin 1) (Fin n) K)
    (C : Matrix (Fin n) (Fin 1) K) (D P L U : Matrix (Fin n) (Fin n) K)
    [Invertible a]
    (hrec : P * (D - C * ⅟a * B) = L * U) :
    liftTrailing P *
        Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks a B C D) =
      assembleLower (P * C * ⅟a) L * assembleUpper a B U := by
  change
    Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks 1 0 0 P) *
        Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks a B C D) =
      Matrix.reindexAlgEquiv K K (headTailEquiv n)
          (Matrix.fromBlocks 1 0 (P * C * ⅟a) L) *
        Matrix.reindexAlgEquiv K K (headTailEquiv n) (Matrix.fromBlocks a B 0 U)
  rw [← map_mul, ← map_mul]
  rw [(Matrix.reindexAlgEquiv K K (headTailEquiv n)).injective.eq_iff]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero,
    Matrix.mul_zero, zero_add]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rw [Matrix.mul_assoc (P * C) (⅟a) a, invOf_mul_self, Matrix.mul_one]
  · rw [← hrec]
    rw [Matrix.mul_sub]
    have hassoc : P * (C * ⅟a * B) = P * C * ⅟a * B := by
      simp [Matrix.mul_assoc]
    rw [hassoc]
    abel

/-- 首次换行与递归置换的乘法方向。
@isnad1 id=eq.0h5v.s9.f55f32090752 from=translated src=- shape=272bb00c vocab=a2375f36
-/
theorem combinedPermutation_mul {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin (n + 1)) (p : Equiv.Perm (Fin n)) :
    (((Equiv.swap 0 i) * liftPermutation p).permMatrix K) * A =
      liftTrailing (p.permMatrix K) * ((Equiv.swap 0 i).permMatrix K * A) := by
  rw [Matrix.permMatrix_mul, liftPermutation_permMatrix, Matrix.mul_assoc]

/-- 把四个块重新组装并返回原来的 `Fin (n+1)` 矩阵。
@isnad1 id=eq.0h3v.s9.8472133438f6 from=translated src=- shape=d2d833bc vocab=d79ef77c
-/
theorem reassembleBlocks {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix.reindexAlgEquiv K K (headTailEquiv n)
        (Matrix.fromBlocks (leadingBlock S) (topRightBlock S)
          (bottomLeftBlock S) (trailingBlock S)) = S := by
  rw [← reindex_eq_fromBlocks]
  change Matrix.reindex (headTailEquiv n) (headTailEquiv n)
      (Matrix.reindex (headTailEquiv n).symm (headTailEquiv n).symm S) = S
  exact (Matrix.reindex (headTailEquiv n) (headTailEquiv n)).apply_symm_apply S

/-- 任意可逆方阵都有单位下三角规范的 PLU 分解。

证明对阶数归纳。每次在首列选非零主元并换到首行，对 Schur 补
递归分解，再用 `recursive_block_product` 组装。
@isnad1 id=nonempty.1h3v.s5.640926e13162 from=translated src=- shape=ffc17d5e vocab=cad438da
-/
theorem existsPLU (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A.det) : Nonempty (PLUFactorization A) := by
  induction n with
  | zero =>
      have hAz : A = 0 := by
        ext i
        exact Fin.elim0 i
      subst A
      exact ⟨pluZero⟩
  | succ n ih =>
      obtain ⟨i, hi⟩ := firstColumn_nonzero A hA
      let S := (Equiv.swap 0 i).permMatrix K * A
      let a := leadingBlock S
      let B := topRightBlock S
      let C := bottomLeftBlock S
      let D := trailingBlock S
      have ha : IsUnit a.det :=
        leadingBlock_isUnit_det _ (pivotPermutation_entry A i |>.trans_ne hi)
      letI := Matrix.invertibleOfIsUnitDet a ha
      let Q : Matrix (Fin n) (Fin n) K := D - C * ⅟a * B
      have hQ : IsUnit Q.det := by
        apply schurComplement_isUnit_det
        rw [← reindex_eq_fromBlocks]
        rw [Matrix.det_submatrix_equiv_self]
        exact pivotPermutation_isUnit_det A hA i
      obtain ⟨rec⟩ := ih Q hQ
      refine ⟨{
        permutation := (Equiv.swap 0 i) * liftPermutation rec.permutation
        lower := assembleLower (rec.permutation.permMatrix K * C * ⅟a) rec.lower
        upper := assembleUpper a B rec.upper
        lower_triangular := assembleLower_lower _ rec.lower_triangular
        upper_triangular := assembleUpper_upper _ _ rec.upper_triangular
        lower_diagonal_one := assembleLower_diag_one _ rec.lower_diagonal_one
        eq_mul := ?_ }⟩
      rw [combinedPermutation_mul]
      change liftTrailing (rec.permutation.permMatrix K) * S = _
      rw [← reassembleBlocks S]
      exact recursive_block_product a B C D (rec.permutation.permMatrix K)
        rec.lower rec.upper rec.eq_mul

/--
@isnad1 id=eq.1h3v.s7.1d644dc65256 from=translated src=- shape=bf3b840b vocab=a563d970
-/
theorem lower_topRight_zero {n : ℕ} {L : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hL : L.IsLowerTriangular) : topRightBlock L = 0 := by
  ext i j
  fin_cases i
  simp only [topRightBlock, Matrix.zero_apply]
  change L 0 j.succ = 0
  exact hL (Fin.succ_pos j)

/--
@isnad1 id=eq.1h3v.s7.347197cc3d47 from=translated src=- shape=91e93ea7 vocab=4037a1a7
-/
theorem upper_bottomLeft_zero {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hU : U.IsUpperTriangular) : bottomLeftBlock U = 0 := by
  ext i j
  fin_cases j
  simp only [bottomLeftBlock, Matrix.zero_apply]
  change U i.succ 0 = 0
  exact hU (Fin.succ_pos i)

/--
@isnad1 id=islowert.1h3v.s6.d797fc6444e6 from=translated src=- shape=694f5d29 vocab=03788b51
-/
theorem trailing_lower {n : ℕ} {L : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hL : L.IsLowerTriangular) : (trailingBlock L).IsLowerTriangular := by
  intro i j hij
  exact hL (Fin.succ_lt_succ_iff.mpr hij)

/--
@isnad1 id=isuppert.1h3v.s6.9b75a15df490 from=translated src=- shape=694f5d29 vocab=c57b6977
-/
theorem trailing_upper {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hU : U.IsUpperTriangular) : (trailingBlock U).IsUpperTriangular := by
  intro i j hij
  exact hU (Fin.succ_lt_succ_iff.mpr hij)

/--
@isnad1 id=eq.1h3v.s7.131793e023fa from=translated src=- shape=40ef3ac0 vocab=994abd1b
-/
theorem leadingBlock_eq_one {n : ℕ} {L : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hd : ∀ i, L i i = 1) : leadingBlock L = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  exact hd 0

/-- 矩阵的首坐标四块分解，写成重索引等价的逆像。
@isnad1 id=eq.0h3v.s10.1a39563cc6a9 from=translated src=- shape=ec3862d4 vocab=f7684a28
-/
theorem blockDecompose {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (Matrix.reindexAlgEquiv K K (headTailEquiv n)).symm M =
      Matrix.fromBlocks (leadingBlock M) (topRightBlock M)
        (bottomLeftBlock M) (trailingBlock M) := by
  exact reindex_eq_fromBlocks M

/-- 两个规范 LU 乘积相等时，比较四个块得到递归唯一性所需的方程。
@isnad1 id=and.7h6v.s10.6913a7299936 from=translated src=- shape=0d9c3fc8 vocab=905da43f
-/
theorem lu_block_equations {n : ℕ}
    (L₁ U₁ L₂ U₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hL₁ : L₁.IsLowerTriangular) (hL₂ : L₂.IsLowerTriangular)
    (hU₁ : U₁.IsUpperTriangular) (hU₂ : U₂.IsUpperTriangular)
    (hdL₁ : ∀ i, L₁ i i = 1) (hdL₂ : ∀ i, L₂ i i = 1)
    (hprod : L₁ * U₁ = L₂ * U₂) :
    leadingBlock U₁ = leadingBlock U₂ ∧
      topRightBlock U₁ = topRightBlock U₂ ∧
      bottomLeftBlock L₁ * leadingBlock U₁ =
        bottomLeftBlock L₂ * leadingBlock U₂ ∧
      bottomLeftBlock L₁ * topRightBlock U₁ +
          trailingBlock L₁ * trailingBlock U₁ =
        bottomLeftBlock L₂ * topRightBlock U₂ +
          trailingBlock L₂ * trailingBlock U₂ := by
  have hb := congrArg (Matrix.reindexAlgEquiv K K (headTailEquiv n)).symm hprod
  simp only [map_mul] at hb
  rw [blockDecompose, blockDecompose, blockDecompose, blockDecompose,
    lower_topRight_zero hL₁, lower_topRight_zero hL₂,
    upper_bottomLeft_zero hU₁, upper_bottomLeft_zero hU₂,
    leadingBlock_eq_one hdL₁, leadingBlock_eq_one hdL₂] at hb
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero,
    Matrix.mul_zero] at hb
  exact Matrix.fromBlocks_inj.mp hb

/-- 单位下三角规范下的 LU 分解唯一。

对阶数归纳：首行确定上三角因子的首行，非零首主元再确定
下三角因子的首列，剩余右下块应用归纳假设。
@isnad1 id=and.8h6v.s8.0ce0ef8041a6 from=translated src=- shape=d145027b vocab=60e7ed6f
-/
theorem lu_unique {n : ℕ}
    (L₁ U₁ L₂ U₂ : Matrix (Fin n) (Fin n) K)
    (hL₁ : L₁.IsLowerTriangular) (hL₂ : L₂.IsLowerTriangular)
    (hU₁ : U₁.IsUpperTriangular) (hU₂ : U₂.IsUpperTriangular)
    (hdL₁ : ∀ i, L₁ i i = 1) (hdL₂ : ∀ i, L₂ i i = 1)
    (hdU₁ : ∀ i, U₁ i i ≠ 0) (hprod : L₁ * U₁ = L₂ * U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  induction n with
  | zero =>
      constructor <;> ext i <;> exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨ha, hB, hCa, htail⟩ :=
        lu_block_equations L₁ U₁ L₂ U₂ hL₁ hL₂ hU₁ hU₂
          hdL₁ hdL₂ hprod
      have hau : IsUnit (leadingBlock U₁).det := by
        rw [Matrix.det_fin_one]
        exact isUnit_iff_ne_zero.mpr (hdU₁ 0)
      have hCa' : bottomLeftBlock L₁ * leadingBlock U₁ =
          bottomLeftBlock L₂ * leadingBlock U₁ := by
        calc
          _ = bottomLeftBlock L₂ * leadingBlock U₂ := hCa
          _ = _ := congrArg (fun M => bottomLeftBlock L₂ * M) ha.symm
      have hC : bottomLeftBlock L₁ = bottomLeftBlock L₂ := by
        calc
          bottomLeftBlock L₁ =
              bottomLeftBlock L₁ * leadingBlock U₁ * (leadingBlock U₁)⁻¹ :=
            (Matrix.mul_nonsing_inv_cancel_right _ _ hau).symm
          _ = bottomLeftBlock L₂ * leadingBlock U₁ * (leadingBlock U₁)⁻¹ :=
            congrArg (fun M => M * (leadingBlock U₁)⁻¹) hCa'
          _ = bottomLeftBlock L₂ := Matrix.mul_nonsing_inv_cancel_right _ _ hau
      have htailprod : trailingBlock L₁ * trailingBlock U₁ =
          trailingBlock L₂ * trailingBlock U₂ := by
        rw [hC, hB] at htail
        exact add_left_cancel htail
      obtain ⟨hLt, hUt⟩ := ih (trailingBlock L₁) (trailingBlock U₁)
        (trailingBlock L₂) (trailingBlock U₂)
        (trailing_lower hL₁) (trailing_lower hL₂)
        (trailing_upper hU₁) (trailing_upper hU₂)
        (fun i => hdL₁ i.succ) (fun i => hdL₂ i.succ)
        (fun i => hdU₁ i.succ) htailprod
      constructor
      · apply (Matrix.reindexAlgEquiv K K (headTailEquiv n)).symm.injective
        rw [blockDecompose, blockDecompose, leadingBlock_eq_one hdL₁,
          leadingBlock_eq_one hdL₂, lower_topRight_zero hL₁,
          lower_topRight_zero hL₂, hC, hLt]
      · apply (Matrix.reindexAlgEquiv K K (headTailEquiv n)).symm.injective
        rw [blockDecompose, blockDecompose, upper_bottomLeft_zero hU₁,
          upper_bottomLeft_zero hU₂, ha, hB, hUt]

/-- 对角矩阵左乘上三角矩阵后仍为上三角。
@isnad1 id=isuppert.1h4v.s6.5a8885497b72 from=translated src=- shape=ad608c7d vocab=9e58663f
-/
theorem diagonal_mul_upper {n : ℕ} (d : Fin n → K)
    {U : Matrix (Fin n) (Fin n) K} (hU : U.IsUpperTriangular) :
    (Matrix.diagonal d * U).IsUpperTriangular := by
  intro i j hij
  rw [Matrix.diagonal_mul]
  rw [hU hij, mul_zero]

/--
@isnad1 id=eq.0h5v.s6.801b28fac2b5 from=translated src=- shape=c24d30fb vocab=c64a99e1
-/
@[simp] theorem diagonal_mul_diag {n : ℕ} (d : Fin n → K)
    (U : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    (Matrix.diagonal d * U) i i = d i * U i i := by
  rw [Matrix.diagonal_mul]

/-- 对角元全部非零时，左乘该对角矩阵可消去。
@isnad1 id=eq.2h5v.s7.2f75c8ca8bc4 from=translated src=- shape=8601188b vocab=c64a99e1
-/
theorem diagonal_mul_injective {n : ℕ} {d : Fin n → K}
    (hd : ∀ i, d i ≠ 0) {A B : Matrix (Fin n) (Fin n) K}
    (h : Matrix.diagonal d * A = Matrix.diagonal d * B) : A = B := by
  ext i j
  have hij := congr_fun (congr_fun h i) j
  simp only [Matrix.diagonal_mul] at hij
  exact mul_left_cancel₀ (hd i) hij

/-- 单位上、下三角规范下的 LDU 分解唯一。
@isnad1 id=and.10h8v.s9.e78bee80bc74 from=translated src=- shape=af3f559f vocab=cc47e89c
-/
theorem ldu_unique {n : ℕ}
    (L₁ U₁ L₂ U₂ : Matrix (Fin n) (Fin n) K) (d₁ d₂ : Fin n → K)
    (hL₁ : L₁.IsLowerTriangular) (hL₂ : L₂.IsLowerTriangular)
    (hU₁ : U₁.IsUpperTriangular) (hU₂ : U₂.IsUpperTriangular)
    (hdL₁ : ∀ i, L₁ i i = 1) (hdL₂ : ∀ i, L₂ i i = 1)
    (hdU₁ : ∀ i, U₁ i i = 1) (hdU₂ : ∀ i, U₂ i i = 1)
    (hnd₁ : ∀ i, d₁ i ≠ 0)
    (hprod : L₁ * Matrix.diagonal d₁ * U₁ =
      L₂ * Matrix.diagonal d₂ * U₂) :
    L₁ = L₂ ∧ d₁ = d₂ ∧ U₁ = U₂ := by
  have hprod' : L₁ * (Matrix.diagonal d₁ * U₁) =
      L₂ * (Matrix.diagonal d₂ * U₂) := by
    simpa only [Matrix.mul_assoc] using hprod
  obtain ⟨hL, hDU⟩ := lu_unique L₁ (Matrix.diagonal d₁ * U₁)
    L₂ (Matrix.diagonal d₂ * U₂) hL₁ hL₂
    (diagonal_mul_upper d₁ hU₁) (diagonal_mul_upper d₂ hU₂)
    hdL₁ hdL₂ (fun i => by simp [hdU₁ i, hnd₁ i]) hprod'
  have hd : d₁ = d₂ := by
    funext i
    have hii := congr_fun (congr_fun hDU i) i
    simpa [hdU₁ i, hdU₂ i] using hii
  subst d₂
  exact ⟨hL, rfl, diagonal_mul_injective hnd₁ hDU⟩

/-- 无换行高斯消元的递归存在条件：每一步 Schur 补的首主元都非零。-/
def NoPivotCondition : (n : ℕ) → Matrix (Fin n) (Fin n) K → Prop
  | 0, _ => True
  | n + 1, A =>
      A 0 0 ≠ 0 ∧
        NoPivotCondition n
          (trailingBlock A - bottomLeftBlock A * (leadingBlock A)⁻¹ * topRightBlock A)

/-- 单位下三角规范的 LU 分解证书。-/
structure NormalizedLUFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) K) where
  lower : Matrix (Fin n) (Fin n) K
  upper : Matrix (Fin n) (Fin n) K
  lower_triangular : lower.IsLowerTriangular
  upper_triangular : upper.IsUpperTriangular
  lower_diagonal_one : ∀ i, lower i i = 1
  upper_diagonal_ne_zero : ∀ i, upper i i ≠ 0
  eq_mul : A = lower * upper

/-- 零阶矩阵的规范 LU 分解。-/
def normalizedLUZero : NormalizedLUFactorization (0 : Matrix (Fin 0) (Fin 0) K) where
  lower := 1
  upper := 1
  lower_triangular := by intro i; exact Fin.elim0 i
  upper_triangular := by intro i; exact Fin.elim0 i
  lower_diagonal_one := by intro i; exact Fin.elim0 i
  upper_diagonal_ne_zero := by intro i; exact Fin.elim0 i
  eq_mul := by ext i; exact Fin.elim0 i

/-- 满足递归非零主元条件的方阵存在无换行的规范 LU 分解。
@isnad1 id=nonempty.1h3v.s4.f76cea0d42e0 from=translated src=- shape=894b9a91 vocab=218db909
-/
theorem exists_normalizedLU_of_noPivot (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (hA : NoPivotCondition n A) : Nonempty (NormalizedLUFactorization A) := by
  induction n with
  | zero =>
      have hAz : A = 0 := by
        ext i
        exact Fin.elim0 i
      subst A
      exact ⟨normalizedLUZero⟩
  | succ n ih =>
      let a := leadingBlock A
      let B := topRightBlock A
      let C := bottomLeftBlock A
      let D := trailingBlock A
      have ha0 : A 0 0 ≠ 0 := hA.1
      have ha : IsUnit a.det := leadingBlock_isUnit_det A ha0
      letI := Matrix.invertibleOfIsUnitDet a ha
      let Q : Matrix (Fin n) (Fin n) K := D - C * ⅟a * B
      have hQ : NoPivotCondition n Q := by
        have hQ' := hA.2
        rw [← Matrix.invOf_eq_nonsing_inv] at hQ'
        exact hQ'
      obtain ⟨rec⟩ := ih Q hQ
      refine ⟨{
        lower := assembleLower (C * ⅟a) rec.lower
        upper := assembleUpper a B rec.upper
        lower_triangular := assembleLower_lower _ rec.lower_triangular
        upper_triangular := assembleUpper_upper _ _ rec.upper_triangular
        lower_diagonal_one := assembleLower_diag_one _ rec.lower_diagonal_one
        upper_diagonal_ne_zero := assembleUpper_diag_ne_zero _ _ ha0 rec.upper_diagonal_ne_zero
        eq_mul := ?_ }⟩
      rw [← reassembleBlocks A]
      have hrec : (1 : Matrix (Fin n) (Fin n) K) * (D - C * ⅟a * B) =
          rec.lower * rec.upper := by
        simpa [Q] using rec.eq_mul
      have hr := recursive_block_product a B C D 1 rec.lower rec.upper hrec
      have hlift : liftTrailing (1 : Matrix (Fin n) (Fin n) K) = 1 := by
        simp [liftTrailing, Matrix.fromBlocks_one]
      rw [hlift, Matrix.one_mul] at hr
      simpa [a, B, C, D] using hr

/-- 规范 LU 分解中上三角因子对角非零，因而原矩阵非奇异。
@isnad1 id=ne.0h4v.s5.196ef1a47e17 from=translated src=- shape=4fcb8e1a vocab=5792e35e
-/
theorem NormalizedLUFactorization.det_ne_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (fac : NormalizedLUFactorization A) : A.det ≠ 0 := by
  rw [fac.eq_mul, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular fac.lower fac.lower_triangular,
    Matrix.det_of_isUpperTriangular fac.upper_triangular]
  simp only [fac.lower_diagonal_one, Finset.prod_const_one, one_mul]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => fac.upper_diagonal_ne_zero i)

/-- 递归非零主元条件特别推出整个矩阵非奇异。
@isnad1 id=ne.1h3v.s5.20d5775c696a from=translated src=- shape=4fcb8e1a vocab=0b306977
-/
theorem det_ne_zero_of_noPivot {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : NoPivotCondition n A) : A.det ≠ 0 := by
  obtain ⟨fac⟩ := exists_normalizedLU_of_noPivot n A hA
  exact fac.det_ne_zero

/-- 左上角 `k × k` 顺序主子矩阵。-/
def leadingPrincipal {n k : ℕ} (A : Matrix (Fin n) (Fin n) K) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) K :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- 教材中的无换行 LU 条件：所有非空顺序主子式均非零。-/
def LeadingPrincipalNonzero {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k (hk : k ≤ n), 0 < k → (leadingPrincipal A hk).det ≠ 0

/-- 顺序主子矩阵首行去掉首元后的右上块。-/
def leadingTopRight {n k : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hk : k ≤ n) : Matrix (Fin 1) (Fin k) K :=
  (topRightBlock A).submatrix id (Fin.castLE hk)

/-- 顺序主子矩阵首列去掉首元后的左下块。-/
def leadingBottomLeft {n k : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hk : k ≤ n) : Matrix (Fin k) (Fin 1) K :=
  (bottomLeftBlock A).submatrix (Fin.castLE hk) id

/-- `(k+1)` 阶顺序主子矩阵的四块表示。
@isnad1 id=eq.1h4v.s8.214ea77ab995 from=translated src=- shape=01fadae4 vocab=add0c72d
-/
theorem leadingPrincipal_succ_blocks {n k : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hk : k ≤ n) :
    (leadingPrincipal A (Nat.succ_le_succ hk)).submatrix
        (headTailEquiv k) (headTailEquiv k) =
      Matrix.fromBlocks (leadingBlock A) (leadingTopRight A hk)
        (leadingBottomLeft A hk) (leadingPrincipal (trailingBlock A) hk) := by
  ext i j
  cases i with
  | inl i =>
      fin_cases i
      cases j with
      | inl j => fin_cases j; rfl
      | inr j => simp [leadingPrincipal, leadingTopRight, topRightBlock]
  | inr i =>
      cases j with
      | inl j =>
          fin_cases j
          simp [leadingPrincipal, leadingBottomLeft, bottomLeftBlock]
      | inr j => simp [leadingPrincipal, trailingBlock]

/-- 取顺序主子矩阵与取首主元的 Schur 补可交换。
@isnad1 id=eq.1h4v.s9.c534764b1223 from=translated src=- shape=be4d4eee vocab=8a6b669a
-/
theorem leadingPrincipal_schur {n k : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hk : k ≤ n) :
    leadingPrincipal
        (trailingBlock A - bottomLeftBlock A * (leadingBlock A)⁻¹ * topRightBlock A) hk =
      leadingPrincipal (trailingBlock A) hk -
        leadingBottomLeft A hk * (leadingBlock A)⁻¹ * leadingTopRight A hk := by
  ext i j
  simp [leadingPrincipal, leadingBottomLeft, leadingTopRight, Matrix.mul_apply]

/-- 顺序主子式的 Schur 递推式：
`Δ_(k+1)(A) = a₁₁ · Δ_k(Schur(A))`。
@isnad1 id=eq.2h4v.s8.64f6073cbbb9 from=translated src=- shape=08f17e36 vocab=b5e0bd83
-/
theorem leadingPrincipal_succ_det {n k : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hk : k ≤ n)
    (ha : A 0 0 ≠ 0) :
    (leadingPrincipal A (Nat.succ_le_succ hk)).det =
      A 0 0 *
        (leadingPrincipal
          (trailingBlock A - bottomLeftBlock A * (leadingBlock A)⁻¹ * topRightBlock A)
          hk).det := by
  have hau : IsUnit (leadingBlock A).det := leadingBlock_isUnit_det A ha
  letI := Matrix.invertibleOfIsUnitDet (leadingBlock A) hau
  have hb := congrArg Matrix.det (leadingPrincipal_succ_blocks A hk)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁] at hb
  rw [hb, Matrix.det_fin_one, leadingBlock_entry, leadingPrincipal_schur]
  rw [Matrix.invOf_eq_nonsing_inv]

/-- 教材中的主子式条件与递归无换行主元条件等价。
@isnad1 id=iff.0h3v.s4.7dbd708c4507 from=translated src=- shape=7b0d2ff4 vocab=4a92da78
-/
theorem noPivot_iff_leadingPrincipalNonzero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    NoPivotCondition n A ↔ LeadingPrincipalNonzero A := by
  induction n with
  | zero =>
      constructor
      · intro _ k hk hk0
        omega
      · intro _
        trivial
  | succ n ih =>
      let Q := trailingBlock A - bottomLeftBlock A * (leadingBlock A)⁻¹ * topRightBlock A
      constructor
      · intro hA k hk hk0
        obtain ⟨ha, hQ⟩ := hA
        cases k with
        | zero => omega
        | succ k =>
            have hkn : k ≤ n := Nat.succ_le_succ_iff.mp hk
            rw [leadingPrincipal_succ_det A hkn ha]
            apply mul_ne_zero ha
            by_cases hk0' : k = 0
            · subst k
              simp [leadingPrincipal]
            · exact (ih Q).mp hQ k hkn (Nat.pos_of_ne_zero hk0')
      · intro hA
        have ha : A 0 0 ≠ 0 := by
          have h1 := hA 1 (Nat.succ_le_succ (Nat.zero_le n)) (by omega)
          simpa [leadingPrincipal, Matrix.det_fin_one] using h1
        refine ⟨ha, (ih Q).mpr ?_⟩
        intro k hk hk0
        have hks : k + 1 ≤ n + 1 := Nat.succ_le_succ hk
        have hbig := hA (k + 1) hks (by omega)
        rw [leadingPrincipal_succ_det A hk ha] at hbig
        exact (mul_ne_zero_iff.mp hbig).2

/-- 教材版无换行 LU 存在定理：若所有非空顺序主子式非零，
则存在单位下三角 `L` 与对角非零的上三角 `U`，使 `A = LU`。
@isnad1 id=nonempty.1h3v.s4.c5b8e1179508 from=translated src=- shape=894b9a91 vocab=aa7d0123
-/
theorem exists_normalizedLU_of_leadingPrincipalNonzero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : LeadingPrincipalNonzero A) :
    Nonempty (NormalizedLUFactorization A) :=
  exists_normalizedLU_of_noPivot n A ((noPivot_iff_leadingPrincipalNonzero A).mpr hA)

/-- 若一个有限和在下标 `k` 以后恒为零，则可把求和域截断为 `Fin k`。
@isnad1 id=eq.2h4v.s6.cfbbb9ded4f6 from=translated src=- shape=e5fbaa49 vocab=ef994dda
-/
theorem sum_fin_eq_sum_castLE {n k : ℕ} (hk : k ≤ n) (f : Fin n → K)
    (hz : ∀ x : Fin n, k ≤ x.val → f x = 0) :
    ∑ x : Fin n, f x = ∑ x : Fin k, f (Fin.castLE hk x) := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      by_cases hkn : k ≤ n
      · have hsum := ih hkn (fun x => f x.castSucc) (by
          intro x hx
          exact hz x.castSucc (by simpa using hx))
        have hcast :
            (∑ x : Fin k, f (Fin.castLE hkn x).castSucc) =
              ∑ x : Fin k, f (Fin.castLE hk x) := by
          congr 1
        rw [Fin.sum_univ_castSucc, hsum, hz (Fin.last n) hkn, add_zero, hcast]
      · have hkeq : k = n + 1 := by omega
        subst k
        congr 1

/-- 三角矩阵乘积的左上顺序主子块等于两个对应主子块的乘积。

证明的关键是：对主子块中的一行，求和下标超出该主子块时，
下三角因子的对应元素恒为零。
@isnad1 id=eq.2h5v.s7.0d98ae976f14 from=translated src=- shape=cf8394f1 vocab=d44ca86a
-/
theorem leadingPrincipal_mul_of_triangular {n k : ℕ}
    (L U : Matrix (Fin n) (Fin n) K) (hk : k ≤ n)
    (hL : L.IsLowerTriangular) :
    leadingPrincipal (L * U) hk = leadingPrincipal L hk * leadingPrincipal U hk := by
  ext i j
  simp only [leadingPrincipal, Matrix.submatrix_apply, Matrix.mul_apply]
  apply sum_fin_eq_sum_castLE hk
  intro x hx
  have hzero : L (Fin.castLE hk i) x = 0 := by
    apply hL
    change (Fin.castLE hk i).val < x.val
    simp only [Fin.val_castLE]
    omega
  rw [hzero, zero_mul]

/-- 下三角矩阵的顺序主子矩阵仍为下三角矩阵。
@isnad1 id=islowert.2h4v.s6.8e67fd3b883e from=translated src=- shape=d298084a vocab=aadc5ccf
-/
theorem leadingPrincipal_isLowerTriangular {n k : ℕ}
    (L : Matrix (Fin n) (Fin n) K) (hk : k ≤ n) (hL : L.IsLowerTriangular) :
    (leadingPrincipal L hk).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  apply hL
  change Fin.castLE hk i < Fin.castLE hk j
  exact hij

/-- 上三角矩阵的顺序主子矩阵仍为上三角矩阵。
@isnad1 id=isuppert.2h4v.s6.061206601355 from=translated src=- shape=d298084a vocab=b60ed895
-/
theorem leadingPrincipal_isUpperTriangular {n k : ℕ}
    (U : Matrix (Fin n) (Fin n) K) (hk : k ≤ n) (hU : U.IsUpperTriangular) :
    (leadingPrincipal U hk).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  apply hU
  change Fin.castLE hk j < Fin.castLE hk i
  exact hij

/-- 任何单位下三角规范 LU 分解都迫使所有非空顺序主子式非零。
@isnad1 id=leadingp.0h4v.s4.b9bbb533026b from=translated src=- shape=5f4831eb vocab=e206f0ab
-/
theorem NormalizedLUFactorization.leadingPrincipalNonzero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (fac : NormalizedLUFactorization A) :
    LeadingPrincipalNonzero A := by
  intro k hk _hk0
  rw [fac.eq_mul, leadingPrincipal_mul_of_triangular fac.lower fac.upper hk
    fac.lower_triangular, Matrix.det_mul]
  rw [Matrix.det_of_isLowerTriangular _
      (leadingPrincipal_isLowerTriangular fac.lower hk fac.lower_triangular),
    Matrix.det_of_isUpperTriangular
      (leadingPrincipal_isUpperTriangular fac.upper hk fac.upper_triangular)]
  simp only [leadingPrincipal, Matrix.submatrix_apply, fac.lower_diagonal_one,
    Finset.prod_const_one, one_mul]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => fac.upper_diagonal_ne_zero _)

/-- 教材中的 LU 存在性判据：方阵存在单位下三角规范 LU 分解，
当且仅当它的每个非空顺序主子式都非零。
@isnad1 id=iff.0h3v.s4.207d0cca2df7 from=translated src=- shape=33d48140 vocab=aa7d0123
-/
theorem leadingPrincipalNonzero_iff_exists_normalizedLU {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    LeadingPrincipalNonzero A ↔ Nonempty (NormalizedLUFactorization A) := by
  constructor
  · exact exists_normalizedLU_of_leadingPrincipalNonzero A
  · rintro ⟨fac⟩
    exact fac.leadingPrincipalNonzero

/-- 单位下三角规范的 LU 分解在两个矩阵因子的层面唯一。
@isnad1 id=and.0h5v.s6.016e685dbcb4 from=translated src=- shape=438c1555 vocab=1f7e1bf8
-/
theorem normalizedLU_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (fac₁ fac₂ : NormalizedLUFactorization A) :
    fac₁.lower = fac₂.lower ∧ fac₁.upper = fac₂.upper :=
  lu_unique fac₁.lower fac₁.upper fac₂.lower fac₂.upper
    fac₁.lower_triangular fac₂.lower_triangular
    fac₁.upper_triangular fac₂.upper_triangular
    fac₁.lower_diagonal_one fac₂.lower_diagonal_one
    fac₁.upper_diagonal_ne_zero (fac₁.eq_mul.symm.trans fac₂.eq_mul)

section Blocks

variable {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- 相对于 `m ⊕ n` 分块的下三角条件：右上块为零。-/
def IsBlockLowerTriangular (M : Matrix (m ⊕ n) (m ⊕ n) K) : Prop :=
  ∀ i j, M (Sum.inl i) (Sum.inr j) = 0

/-- 相对于 `m ⊕ n` 分块的上三角条件：左下块为零。-/
def IsBlockUpperTriangular (M : Matrix (m ⊕ n) (m ⊕ n) K) : Prop :=
  ∀ i j, M (Sum.inr i) (Sum.inl j) = 0

/-- 块对角条件：两个非对角块均为零。-/
def IsBlockDiagonal (M : Matrix (m ⊕ n) (m ⊕ n) K) : Prop :=
  IsBlockLowerTriangular M ∧ IsBlockUpperTriangular M

/-- Schur 补给出的分块 LDU 分解。左上块可逆正是本次消元可选取该主元块的条件。-/
def blockLDU (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    LDUFactorization (Matrix.fromBlocks A B C D) where
  lower := Matrix.fromBlocks 1 0 (C * ⅟A) 1
  diagonal := Matrix.fromBlocks A 0 0 (D - C * ⅟A * B)
  upper := Matrix.fromBlocks 1 (⅟A * B) 0 1
  eq_mul := Matrix.fromBlocks_eq_of_invertible₁₁ A B C D

/--
@isnad1 id=eq.0h7v.s8.be88e057bcf9 from=translated src=- shape=f87044e1 vocab=ec034f8d
-/
@[simp] theorem blockLDU_lower (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    (blockLDU A B C D).lower = Matrix.fromBlocks 1 0 (C * ⅟A) 1 := rfl

/--
@isnad1 id=eq.0h7v.s8.3cb8352e8273 from=translated src=- shape=c2dfe943 vocab=dba77117
-/
@[simp] theorem blockLDU_diagonal (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    (blockLDU A B C D).diagonal =
      Matrix.fromBlocks A 0 0 (D - C * ⅟A * B) := rfl

/--
@isnad1 id=eq.0h7v.s8.95f09eeb6ff3 from=translated src=- shape=4b20022c vocab=31a6299c
-/
@[simp] theorem blockLDU_upper (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    (blockLDU A B C D).upper = Matrix.fromBlocks 1 (⅟A * B) 0 1 := rfl

/-- Schur 补构造的第一个因子确为块下三角矩阵。
@isnad1 id=isblockl.0h7v.s7.d94c8bb9b892 from=translated src=- shape=8248df15 vocab=0051a060
-/
theorem blockLDU_isBlockLowerTriangular (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    IsBlockLowerTriangular (blockLDU A B C D).lower := by
  intro i j
  rfl

/-- Schur 补构造的中间因子确为块对角矩阵。
@isnad1 id=isblockd.0h7v.s7.392937e3a67a from=translated src=- shape=8248df15 vocab=59aa18ef
-/
theorem blockLDU_isBlockDiagonal (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    IsBlockDiagonal (blockLDU A B C D).diagonal := by
  constructor <;> intro i j <;> rfl

/-- Schur 补构造的第三个因子确为块上三角矩阵。
@isnad1 id=isblocku.0h7v.s7.bb321b2686dd from=translated src=- shape=8248df15 vocab=44220ca9
-/
theorem blockLDU_isBlockUpperTriangular (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    IsBlockUpperTriangular (blockLDU A B C D).upper := by
  intro i j
  rfl

/-- 合并 LDU 的后两个因子即可得到块 LU 分解。-/
def blockLU (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    LUFactorization (Matrix.fromBlocks A B C D) where
  lower := (blockLDU A B C D).lower
  upper := (blockLDU A B C D).diagonal * (blockLDU A B C D).upper
  eq_mul := by
    calc
      Matrix.fromBlocks A B C D =
          (blockLDU A B C D).lower * (blockLDU A B C D).diagonal *
            (blockLDU A B C D).upper := (blockLDU A B C D).eq_mul
      _ = (blockLDU A B C D).lower *
          ((blockLDU A B C D).diagonal * (blockLDU A B C D).upper) :=
        Matrix.mul_assoc _ _ _

/--
@isnad1 id=eq.0h7v.s8.5f5d75ae856d from=translated src=- shape=f87044e1 vocab=f8cf6372
-/
@[simp] theorem blockLU_lower (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) [Invertible A] :
    (blockLU A B C D).lower = Matrix.fromBlocks 1 0 (C * ⅟A) 1 := rfl

end Blocks

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
