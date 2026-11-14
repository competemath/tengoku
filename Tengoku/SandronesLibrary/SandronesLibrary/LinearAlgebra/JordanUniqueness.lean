/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.JordanSimilarity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / JordanUniqueness —— Jordan 块的唯一性

Jordan 标准形的块没有自然顺序，因此“唯一”不能表述为两份 `JordanFormData` 字面相等。
本文件把每个块编码为“特征值—块长度”标签，并首先证明组合学唯一性：若每种标签
出现的重数相同，则两份块数据之间存在保持全部标签的重编号。

后续的线性代数部分将通过广义特征空间中 `(T - μI)^k` 的核维数恢复这些重数。

> **Entry**: linear-algebra.eigen.jordan-uniqueness
-/

namespace SandronesLibrary.LinearAlgebra.Jordan

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.Coordinates

variable {K : Type*}

/-- Jordan 块的完整标签：特征值与块参数；实际块大小为参数加一。-/
def JordanFormData.blockLabel (d : JordanFormData K) (i : d.Block) : K × ℕ :=
  (d.eigenvalue i, d.length i)

/-- 两份 Jordan 数据等价，意为它们仅相差块的重编号。-/
def JordanFormData.Equivalent (d₁ d₂ : JordanFormData K) : Prop :=
  ∃ e : d₁.Block ≃ d₂.Block,
    ∀ i, d₂.blockLabel (e i) = d₁.blockLabel i

/-- 每种“特征值—块长度”标签的重数确定 Jordan 数据，不计块的排列顺序。-/
theorem jordanFormData_equivalent_of_fiber_card_eq
    (d₁ d₂ : JordanFormData K)
    (h : ∀ c : K × ℕ,
      Nat.card {i : d₁.Block // d₁.blockLabel i = c} =
        Nat.card {i : d₂.Block // d₂.blockLabel i = c}) :
    d₁.Equivalent d₂ := by
  letI := d₁.blockFintype
  letI := d₂.blockFintype
  classical
  let fiberEquiv (c : K × ℕ) :
      {i : d₁.Block // d₁.blockLabel i = c} ≃
        {i : d₂.Block // d₂.blockLabel i = c} :=
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_eq_nat_card] using h c)
  let e : d₁.Block ≃ d₂.Block := Equiv.ofFiberEquiv fiberEquiv
  refine ⟨e, ?_⟩
  intro i
  exact Equiv.ofFiberEquiv_map fiberEquiv i

/-- 特征值为 `μ` 且大小严格大于 `k` 的 Jordan 块数。-/
noncomputable def JordanFormData.blockTailCount
    (d : JordanFormData K) (μ : K) (k : ℕ) : ℕ := by
  letI := d.blockFintype
  classical
  exact (Finset.univ.filter fun i : d.Block =>
    d.eigenvalue i = μ ∧ k < d.length i + 1).card

/-- 给定特征值与长度参数的 Jordan 块重数。-/
noncomputable def JordanFormData.blockMultiplicity
    (d : JordanFormData K) (μ : K) (m : ℕ) : ℕ := by
  letI := d.blockFintype
  classical
  exact (Finset.univ.filter fun i : d.Block =>
    d.eigenvalue i = μ ∧ d.length i = m).card

/-- 尾计数的相邻差给出大小恰为 `m+1` 的块数。-/
theorem blockTailCount_eq_multiplicity_add_succ
    (d : JordanFormData K) (μ : K) (m : ℕ) :
    d.blockTailCount μ m =
      d.blockMultiplicity μ m + d.blockTailCount μ (m + 1) := by
  letI := d.blockFintype
  classical
  let A := Finset.univ.filter fun i : d.Block =>
    d.eigenvalue i = μ ∧ m < d.length i + 1
  let B := Finset.univ.filter fun i : d.Block =>
    d.eigenvalue i = μ ∧ d.length i = m
  let C := Finset.univ.filter fun i : d.Block =>
    d.eigenvalue i = μ ∧ m + 1 < d.length i + 1
  have hA : A = B ∪ C := by
    ext i
    simp only [A, B, C, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · rintro ⟨hμ, hm⟩
      have hor : d.length i = m ∨ m + 1 < d.length i + 1 := by omega
      rcases hor with heq | hgt
      · exact Or.inl ⟨hμ, heq⟩
      · exact Or.inr ⟨hμ, hgt⟩
    · rintro (⟨hμ, rfl⟩ | ⟨hμ, hm⟩)
      · exact ⟨hμ, by omega⟩
      · exact ⟨hμ, by omega⟩
  have hdisjoint : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro i hiB hiC
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hiB
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hiC
    omega
  change A.card = B.card + C.card
  rw [hA]
  exact Finset.card_union_of_disjoint hdisjoint

/-- 若两份 Jordan 数据的全部尾计数相同，则每种块标签的重数相同。-/
theorem blockMultiplicity_eq_of_tailCount_eq
    (d₁ d₂ : JordanFormData K)
    (h : ∀ μ k, d₁.blockTailCount μ k = d₂.blockTailCount μ k) :
    ∀ μ m, d₁.blockMultiplicity μ m = d₂.blockMultiplicity μ m := by
  intro μ m
  have h₁ := blockTailCount_eq_multiplicity_add_succ d₁ μ m
  have h₂ := blockTailCount_eq_multiplicity_add_succ d₂ μ m
  rw [h μ m, h μ (m + 1)] at h₁
  omega

/-- `blockMultiplicity` 就是相应标签纤维的基数。-/
theorem natCard_blockLabel_fiber
    (d : JordanFormData K) (μ : K) (m : ℕ) :
    Nat.card {i : d.Block // d.blockLabel i = (μ, m)} =
      d.blockMultiplicity μ m := by
  letI := d.blockFintype
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [JordanFormData.blockMultiplicity, JordanFormData.blockLabel,
    Prod.mk.injEq]

/-- 全部尾计数确定 Jordan 标准形的块数据，唯一性只差块排列。-/
theorem jordanFormData_equivalent_of_tailCount_eq
    (d₁ d₂ : JordanFormData K)
    (h : ∀ μ k, d₁.blockTailCount μ k = d₂.blockTailCount μ k) :
    d₁.Equivalent d₂ := by
  apply jordanFormData_equivalent_of_fiber_card_eq
  rintro ⟨μ, m⟩
  rw [natCard_blockLabel_fiber, natCard_blockLabel_fiber]
  exact blockMultiplicity_eq_of_tailCount_eq d₁ d₂ h μ m

/-- Jordan 数据在 `(μ,k)` 处给出的广义核维数候选公式：每个 `μ`-块贡献
`min k size`，其他特征值的块不贡献核。-/
noncomputable def JordanFormData.kernelProfile
    (d : JordanFormData K) (μ : K) (k : ℕ) : ℕ := by
  letI := d.blockFintype
  classical
  exact ∑ i : d.Block,
    if d.eigenvalue i = μ then min k (d.length i + 1) else 0

/-- 块公式的相邻增量是大小超过 `k` 的块数。-/
theorem kernelProfile_succ_sub_eq_blockTailCount
    (d : JordanFormData K) (μ : K) (k : ℕ) :
    d.kernelProfile μ (k + 1) - d.kernelProfile μ k =
      d.blockTailCount μ k := by
  letI := d.blockFintype
  classical
  change
    (∑ i : d.Block,
      if d.eigenvalue i = μ then min (k + 1) (d.length i + 1) else 0) -
        (∑ i : d.Block,
          if d.eigenvalue i = μ then min k (d.length i + 1) else 0) =
      (Finset.univ.filter fun i : d.Block =>
        d.eigenvalue i = μ ∧ k < d.length i + 1).card
  have hsum :
      (∑ i : d.Block,
        if d.eigenvalue i = μ then min (k + 1) (d.length i + 1) else 0) =
        (∑ i : d.Block,
          if d.eigenvalue i = μ then min k (d.length i + 1) else 0) +
        (Finset.univ.filter fun i : d.Block =>
          d.eigenvalue i = μ ∧ k < d.length i + 1).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hμ : d.eigenvalue i = μ
    · by_cases hk : k < d.length i + 1
      · have hk1 : k + 1 ≤ d.length i + 1 := by omega
        have hk0 : k ≤ d.length i + 1 := by omega
        simp [hμ, hk, min_eq_left hk1, min_eq_left hk0]
      · have hle : d.length i + 1 ≤ k := by omega
        have hle1 : d.length i + 1 ≤ k + 1 := by omega
        simp [hμ, hk, min_eq_right hle, min_eq_right hle1]
    · simp [hμ]
  omega

/-- `(T-μI)^k` 的核维数；这是 Jordan 块大小唯一性的内禀不变量。-/
noncomputable def generalizedKernelDimension
    {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (T : V →ₗ[K] V) (μ : K) (k : ℕ) : ℕ :=
  Module.finrank K (LinearMap.ker ((T - μ • LinearMap.id) ^ k))

/-- 方阵所表示算子的广义核维数，以秩—零度公式写成“维数减秩”。-/
noncomputable def matrixGeneralizedKernelDimension
    [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (μ : K) (k : ℕ) : ℕ :=
  Fintype.card ι - Matrix.rank ((A - Matrix.scalar ι μ) ^ k)

/-- 换到任意一组基不改变广义核维数。-/
theorem generalizedKernelDimension_eq_matrix
    {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    [IsFiniteDimensional K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : V →ₗ[K] V) (b : ι → V) (hb : IsBasis K b)
    (μ : K) (k : ℕ) :
    generalizedKernelDimension T μ k =
      matrixGeneralizedKernelDimension (operatorMatrix b hb T) μ k := by
  classical
  let B : Module.Basis ι K V := Module.Basis.mk hb.1 (by simpa [hb.2])
  let F : V →ₗ[K] V := (T - μ • LinearMap.id) ^ k
  have hscalar :
      LinearMap.toMatrix B B (μ • LinearMap.id) = Matrix.scalar ι μ := by
    rw [← Module.algebraMap_end_eq_smul_id,
      LinearMap.toMatrix_algebraMap]
  have hmatrix :
      (operatorMatrix b hb T - Matrix.scalar ι μ) ^ k =
        LinearMap.toMatrix B B F := by
    change
      (LinearMap.toMatrix B B T - Matrix.scalar ι μ) ^ k =
        LinearMap.toMatrix B B F
    rw [← hscalar, ← map_sub, LinearMap.toMatrix_pow]
  have hrank :
      Matrix.rank ((operatorMatrix b hb T - Matrix.scalar ι μ) ^ k) =
        Module.finrank K (LinearMap.range F) := by
    rw [hmatrix, Matrix.rank_eq_finrank_range_toLin _ B B,
      Matrix.toLin_toMatrix]
  have hdim : Module.finrank K V = Fintype.card ι := by
    simpa [B] using (Module.finrank_eq_card_basis B)
  have hnullity := F.finrank_range_add_finrank_ker
  simp only [generalizedKernelDimension, matrixGeneralizedKernelDimension]
  rw [hrank]
  change Module.finrank K (LinearMap.ker F) =
    Fintype.card ι - Module.finrank K (LinearMap.range F)
  omega

/-- Jordan 标准矩阵减去标量矩阵并取幂，仍逐块计算。-/
theorem jordanNormalMatrix_shift_pow_eq_blockDiagonal
    [Field K] (d : JordanFormData K) [Fintype d.Block] [DecidableEq d.Block]
    (μ : K) (k : ℕ) :
    (jordanNormalMatrix d -
        Matrix.scalar (Σ i : d.Block, Fin (d.length i + 1)) μ) ^ k =
      Matrix.blockDiagonal' (fun i =>
        (jordanBlock (d.eigenvalue i) (d.length i) -
          Matrix.scalar (Fin (d.length i + 1)) μ) ^ k) := by
  have hbase :
      jordanNormalMatrix d -
          Matrix.scalar (Σ i : d.Block, Fin (d.length i + 1)) μ =
        Matrix.blockDiagonal' (fun i =>
          jordanBlock (d.eigenvalue i) (d.length i) -
            Matrix.scalar (Fin (d.length i + 1)) μ) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      by_cases hab : a = b
      · subst b
        simp [jordanNormalMatrix, Matrix.blockDiagonal'_apply]
      · have hsigma : (⟨i, a⟩ : Σ i, Fin (d.length i + 1)) ≠ ⟨i, b⟩ := by
          intro h
          exact hab (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        simp [jordanNormalMatrix, Matrix.blockDiagonal'_apply, hab, hsigma]
    · simp [jordanNormalMatrix, Matrix.blockDiagonal'_apply, hij]
  calc
    _ = (Matrix.blockDiagonal' (fun i =>
        jordanBlock (d.eigenvalue i) (d.length i) -
          Matrix.scalar (Fin (d.length i + 1)) μ)) ^ k := congrArg (· ^ k) hbase
    _ = _ := (Matrix.blockDiagonal'_pow _ k).symm

/-- 若移去的标量不同于 Jordan 块特征值，则移位块及其任意幂都可逆，因而秩满。-/
theorem jordanBlock_shift_pow_rank_of_ne
    [Field K] (lam μ : K) (m k : ℕ) (h : lam ≠ μ) :
    Matrix.rank ((jordanBlock lam m - Matrix.scalar (Fin (m + 1)) μ) ^ k) =
      m + 1 := by
  classical
  let A := jordanBlock lam m - Matrix.scalar (Fin (m + 1)) μ
  have hupper : A.IsUpperTriangular := by
    intro i j hji
    change j.val < i.val at hji
    have hij : i ≠ j := by
      intro heq
      subst j
      omega
    have hsucc : i.val + 1 ≠ j.val := by omega
    simp [A, jordanBlock, hij, hsucc, Matrix.diagonal_apply_ne]
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    simp [A, jordanBlock]
    exact sub_ne_zero.mpr h
  have hdetpow : (A ^ k).det ≠ 0 := by
    rw [Matrix.det_pow]
    exact pow_ne_zero _ hdet
  simpa [A] using Matrix.rank_of_det_ne_zero hdetpow

/-- 纯幂零 Jordan 移位块的 `k` 次幂只在第 `k` 条上对角线上取值一。-/
theorem jordanBlock_nilpotent_shift_pow_apply
    [Field K] (μ : K) (m k : ℕ) (i j : Fin (m + 1)) :
    ((jordanBlock μ m - Matrix.scalar (Fin (m + 1)) μ) ^ k) i j =
      if i.val + k = j.val then 1 else 0 := by
  classical
  have hN (a b : Fin (m + 1)) :
      (jordanBlock μ m - Matrix.scalar (Fin (m + 1)) μ) a b =
        if a.val + 1 = b.val then 1 else 0 := by
    by_cases hab : a = b
    · subst b
      simp [jordanBlock]
    · simp [jordanBlock, hab]
  induction k generalizing i j with
  | zero =>
      simp [Matrix.one_apply, Fin.ext_iff]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih, hN]
      by_cases hik : i.val + k < m + 1
      · let a : Fin (m + 1) := ⟨i.val + k, hik⟩
        rw [Finset.sum_eq_single a]
        · simp [a, Nat.add_assoc]
        · intro b _hb hba
          have hne : i.val + k ≠ b.val := by
            intro heq
            apply hba
            exact Fin.ext heq.symm
          simp [hne]
        · simp
      · have hzero : ∀ a : Fin (m + 1), i.val + k ≠ a.val := by
          intro a heq
          omega
        have hsucczero : i.val + (k + 1) ≠ j.val := by omega
        simp [hzero, hsucczero]

/-- 只有第 `k` 条上对角线为一的移位矩阵的秩为 `n-min(k,n)`。-/
theorem rank_eq_card_sub_min_of_shift_entries
    [Field K] {n k : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, A i j = if i.val + k = j.val then 1 else 0) :
    Matrix.rank A = n - min k n := by
  classical
  let I := {i : Fin n // i.val + k < n}
  let target : I → Fin n := fun i => ⟨i.1.val + k, i.2⟩
  have htarget : Function.Injective target := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change i.1.val + k = j.1.val + k at hv
    omega
  let rows : I → (Fin n → K) := fun i => Pi.single (target i) 1
  have hrows : LinearIndependent K rows := by
    exact (Pi.linearIndependent_single_one (R := K) (ι := Fin n)).comp
      target htarget
  have hrow_valid (i : I) : A.row i.1 = rows i := by
    ext j
    simp [Matrix.row, rows, target, hA, Pi.single_apply, Fin.ext_iff, eq_comm]
  have hrow_invalid (i : Fin n) (hi : ¬i.val + k < n) : A.row i = 0 := by
    ext j
    change A i j = 0
    rw [hA]
    simp only [ite_eq_right_iff]
    intro heq
    omega
  have hspan :
      Submodule.span K (Set.range A.row) =
        Submodule.span K (Set.range rows) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro v hv
      obtain ⟨i, rfl⟩ := hv
      by_cases hi : i.val + k < n
      · have heq : A.row i = rows (⟨i, hi⟩ : I) := hrow_valid ⟨i, hi⟩
        rw [heq]
        exact Submodule.subset_span (Set.mem_range_self _)
      · rw [hrow_invalid i hi]
        exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      intro v hv
      obtain ⟨i, rfl⟩ := hv
      rw [← hrow_valid i]
      exact Submodule.subset_span (Set.mem_range_self _)
  have hrank : Matrix.rank A = Fintype.card I := by
    rw [Matrix.rank_eq_finrank_span_row, hspan]
    exact (linearIndependent_iff_card_eq_finrank_span.mp hrows).symm
  let e : I ≃ Fin (n - k) :=
    { toFun := fun i => ⟨i.1.val, Nat.lt_sub_of_add_lt i.2⟩
      invFun := fun i => by
        have hp : i.val + k < n := Nat.add_lt_of_lt_sub i.isLt
        exact ⟨⟨i.val, lt_of_le_of_lt (Nat.le_add_right _ _) hp⟩, hp⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  have hcard : Fintype.card I = n - k := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  rw [hrank, hcard]
  omega

/-- 纯幂零 Jordan 移位块的 `k` 次幂秩。-/
theorem jordanBlock_nilpotent_shift_pow_rank
    [Field K] [DecidableEq K] (μ : K) (m k : ℕ) :
    Matrix.rank ((jordanBlock μ m - Matrix.scalar (Fin (m + 1)) μ) ^ k) =
      (m + 1) - min k (m + 1) := by
  apply rank_eq_card_sub_min_of_shift_entries
  exact jordanBlock_nilpotent_shift_pow_apply μ m k

/-- 单 Jordan 块移去标量后取幂的完整秩公式。-/
theorem jordanBlock_shift_pow_rank
    [Field K] [DecidableEq K] (lam μ : K) (m k : ℕ) :
    Matrix.rank ((jordanBlock lam m - Matrix.scalar (Fin (m + 1)) μ) ^ k) =
      if lam = μ then (m + 1) - min k (m + 1) else m + 1 := by
  by_cases h : lam = μ
  · subst lam
    rw [ite_eq_left rfl]
    exact jordanBlock_nilpotent_shift_pow_rank μ m k
  · rw [ite_eq_right h]
    exact jordanBlock_shift_pow_rank_of_ne lam μ m k h

/-- 块对角矩阵作用在向量上的第 `(i,j)` 个坐标，只由第 `i` 块决定。-/
theorem blockDiagonal_toLin_apply
    [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (A : ∀ i, Matrix (n i) (n i) K)
    (x : (Σ i, n i) → K) (i : ι) (j : n i) :
    Matrix.toLin' (Matrix.blockDiagonal' A) x ⟨i, j⟩ =
      Matrix.toLin' (A i) (fun q => x ⟨i, q⟩) j := by
  classical
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp [Matrix.blockDiagonal'_apply]

/-- 块对角矩阵的秩是各对角块秩之和。-/
theorem rank_blockDiagonal'
    [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (A : ∀ i, Matrix (n i) (n i) K) :
    Matrix.rank (Matrix.blockDiagonal' A) = ∑ i, Matrix.rank (A i) := by
  classical
  let G : ((Σ i, n i) → K) →ₗ[K] ((Σ i, n i) → K) :=
    Matrix.toLin' (Matrix.blockDiagonal' A)
  let f (i : ι) : (n i → K) →ₗ[K] (n i → K) := Matrix.toLin' (A i)
  let E : LinearMap.range G ≃ₗ[K] ∀ i, LinearMap.range (f i) :=
    { toFun := fun y i => by
        refine ⟨fun j => y.1 ⟨i, j⟩, ?_⟩
        obtain ⟨x, hx⟩ := y.2
        refine ⟨fun q => x ⟨i, q⟩, ?_⟩
        ext j
        change Matrix.toLin' (A i) (fun q => x ⟨i, q⟩) j = y.1 ⟨i, j⟩
        rw [← blockDiagonal_toLin_apply A x i j, hx]
      invFun := fun y => by
        let pre (i : ι) : n i → K := (y i).2.choose
        let x : (Σ i, n i) → K := fun q => pre q.1 q.2
        refine ⟨fun q => (y q.1).1 q.2, ?_⟩
        refine ⟨x, ?_⟩
        ext ⟨i, j⟩
        rw [blockDiagonal_toLin_apply A x i j]
        exact congrFun (y i).2.choose_spec j
      left_inv := by
        intro y
        ext ⟨i, j⟩
        rfl
      right_inv := by
        intro y
        ext i j
        rfl
      map_add' := by
        intro y z
        ext i j
        rfl
      map_smul' := by
        intro c y
        ext i j
        rfl }
  change Module.finrank K (LinearMap.range G) =
    ∑ i, Module.finrank K (LinearMap.range (f i))
  rw [E.finrank_eq, Module.finrank_pi_fintype]

/-- Jordan 块对角矩阵的广义核维数由逐块的 `min k size` 求和给出。-/
theorem jordanNormalMatrix_generalizedKernelDimension
    [Field K] (d : JordanFormData K) [Fintype d.Block] [DecidableEq d.Block]
    (μ : K) (k : ℕ) :
    matrixGeneralizedKernelDimension (jordanNormalMatrix d) μ k =
      d.kernelProfile μ k := by
  classical
  unfold matrixGeneralizedKernelDimension
  rw [jordanNormalMatrix_shift_pow_eq_blockDiagonal,
    rank_blockDiagonal']
  have hcard :
      Fintype.card (Σ i : d.Block, Fin (d.length i + 1)) =
        ∑ i : d.Block, (d.length i + 1) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
  rw [hcard]
  have hranks : (∑ i : d.Block,
      Matrix.rank ((jordanBlock (d.eigenvalue i) (d.length i) -
        Matrix.scalar (Fin (d.length i + 1)) μ) ^ k)) =
      ∑ i : d.Block, if d.eigenvalue i = μ then
        (d.length i + 1) - min k (d.length i + 1) else d.length i + 1 := by
    apply Fintype.sum_congr
    intro i
    exact jordanBlock_shift_pow_rank _ _ _ _
  rw [hranks]
  unfold JordanFormData.kernelProfile
  have hsum :
      (∑ i : d.Block, (d.length i + 1)) =
        (∑ i : d.Block,
          if d.eigenvalue i = μ then
            (d.length i + 1) - min k (d.length i + 1)
          else d.length i + 1) +
        ∑ i : d.Block,
          if d.eigenvalue i = μ then min k (d.length i + 1) else 0 := by
    calc
      _ = ∑ i : d.Block,
          ((if d.eigenvalue i = μ then
              (d.length i + 1) - min k (d.length i + 1)
            else d.length i + 1) +
            if d.eigenvalue i = μ then min k (d.length i + 1) else 0) := by
          apply Fintype.sum_congr
          intro i
          by_cases hμ : d.eigenvalue i = μ
          · simp [hμ, Nat.sub_add_cancel (min_le_right k (d.length i + 1))]
          · simp [hμ]
      _ = _ := Finset.sum_add_distrib
  rw [hsum, Nat.add_sub_cancel_left]
  have hF : (inferInstance : Fintype d.Block) = d.blockFintype :=
    Subsingleton.elim _ _
  cases hF
  rfl

/-- 换到一组 Jordan 标准基后，内禀广义核维数等于块公式。-/
theorem generalizedKernelDimension_eq_kernelProfile
    {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (d : JordanFormData K)
    (hd : HasJordanNormalBasis T d) (μ : K) (k : ℕ) :
    generalizedKernelDimension T μ k = d.kernelProfile μ k := by
  letI := d.blockFintype
  classical
  obtain ⟨b, hb, hmatrix⟩ := hd
  rw [generalizedKernelDimension_eq_matrix T b hb μ k, hmatrix]
  exact jordanNormalMatrix_generalizedKernelDimension d μ k

/-- 一份 Jordan 基中大小超过 `k` 的 `μ`-块数，是相邻广义核维数之差。-/
theorem blockTailCount_eq_generalizedKernelDimension_sub
    {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (d : JordanFormData K)
    (hd : HasJordanNormalBasis T d) (μ : K) (k : ℕ) :
    d.blockTailCount μ k =
      generalizedKernelDimension T μ (k + 1) -
        generalizedKernelDimension T μ k := by
  rw [generalizedKernelDimension_eq_kernelProfile T d hd μ (k + 1),
    generalizedKernelDimension_eq_kernelProfile T d hd μ k,
    kernelProfile_succ_sub_eq_blockTailCount]

/-- 同一算子的任意两份 Jordan 标准基给出相同的全部块尾计数。-/
theorem blockTailCount_eq_of_hasJordanNormalBasis
    {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (d₁ d₂ : JordanFormData K)
    (h₁ : HasJordanNormalBasis T d₁)
    (h₂ : HasJordanNormalBasis T d₂) :
    ∀ μ k, d₁.blockTailCount μ k = d₂.blockTailCount μ k := by
  intro μ k
  rw [blockTailCount_eq_generalizedKernelDimension_sub T d₁ h₁ μ k,
    blockTailCount_eq_generalizedKernelDimension_sub T d₂ h₂ μ k]

/-- **Jordan 标准形唯一性**：同一算子的两份 Jordan 块数据仅相差块的排列。-/
theorem jordan_normal_basis_unique
    {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (d₁ d₂ : JordanFormData K)
    (h₁ : HasJordanNormalBasis T d₁)
    (h₂ : HasJordanNormalBasis T d₂) :
    d₁.Equivalent d₂ := by
  apply jordanFormData_equivalent_of_tailCount_eq
  exact blockTailCount_eq_of_hasJordanNormalBasis T d₁ d₂ h₁ h₂

end SandronesLibrary.LinearAlgebra.Jordan
