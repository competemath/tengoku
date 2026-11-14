/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Diagonalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / Jordan —— 广义特征空间与 Jordan 链基础

本文件建立 Jordan 标准形之前可独立验证的教材基础：广义特征空间及其层级关系、
Jordan 链基、Jordan 块矩阵表示，以及链向量被相应幂次湮灭。完整 Jordan 标准形的
存在性在后续 `JordanDecomposition`、`JordanNormalForm` 与 `JordanSimilarity` 中完成。
公开签名不暴露 mathlib 的模或子模结构。

> **Entry**: linear-algebra.eigen.jordan
-/

namespace SandronesLibrary.LinearAlgebra.Jordan

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.Eigenvalue
open SandronesLibrary.LinearAlgebra.Coordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

/-- 属于 `μ` 的 `k` 阶广义特征子空间。-/
def generalizedEigenspace (T : V →ₗ[K] V) (μ : K) (k : ℕ) : Set V :=
  {x | ((T - μ • (LinearMap.id : V →ₗ[K] V)) ^ k) x = 0}

/-- 广义特征子空间确实是子空间。-/
theorem generalizedEigenspace_isSubspace (T : V →ₗ[K] V) (μ : K) (k : ℕ) :
    IsSubspace K (generalizedEigenspace T μ k) := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  refine ⟨⟨0, by simp [generalizedEigenspace, A]⟩, ?_, ?_⟩
  · intro x hx y hy
    change (A ^ k) x = 0 at hx
    change (A ^ k) y = 0 at hy
    change (A ^ k) (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  · intro c x hx
    change (A ^ k) x = 0 at hx
    change (A ^ k) (c • x) = 0
    rw [map_smul, hx, smul_zero]

/-- 一级广义特征子空间就是通常的特征子空间。-/
theorem generalizedEigenspace_one (T : V →ₗ[K] V) (μ : K) :
    generalizedEigenspace T μ 1 = eigenspace K T μ := by
  ext x
  simp [generalizedEigenspace, eigenspace, LinearMap.sub_apply, sub_eq_zero]

/-- 广义特征子空间随阶数增加而扩大。-/
theorem generalizedEigenspace_mono (T : V →ₗ[K] V) (μ : K) {k l : ℕ}
    (hkl : k ≤ l) : generalizedEigenspace T μ k ⊆ generalizedEigenspace T μ l := by
  intro x hx
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  change (A ^ k) x = 0 at hx
  change (A ^ (k + d)) x = 0
  rw [add_comm k d, pow_add, Module.End.mul_apply, hx, map_zero]

/-- **广义特征子空间稳定定理**：有限维空间中，到 `dim V` 阶时广义特征子空间
已经稳定；任何更高阶都不会再产生新向量。-/
theorem generalizedEigenspace_stabilizes [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (μ : K) {k : ℕ} (hk : dim K V ≤ k) :
    generalizedEigenspace T μ k = generalizedEigenspace T μ (dim K V) := by
  have h := Module.End.genEigenspace_eq_genEigenspace_finrank_of_le T μ hk
  ext x
  have hx := SetLike.ext_iff.mp h x
  simpa [generalizedEigenspace, Module.End.mem_genEigenspace_nat, dim,
    Module.End.one_eq_id] using hx

/-- **广义特征空间分解的张成形式**：在代数闭域上，所有特征值对应的最大广义
特征子空间共同张成整个有限维空间。

这里“最大”可统一取 `dim V` 阶。这个集合式陈述避免在教材接口中暴露子模上确界，
并为后续在每个广义特征子空间内构造 Jordan 链基提供全空间组装入口。-/
theorem span_generalizedEigenvectors_eq_univ [IsFiniteDimensional K V] [IsAlgClosed K]
    (T : V →ₗ[K] V) :
    span K {x : V | ∃ μ : K, x ∈ generalizedEigenspace T μ (dim K V)} =
      Set.univ := by
  let G : Set V := {x : V | ∃ μ : K, x ∈ generalizedEigenspace T μ (dim K V)}
  let P : Submodule K V := Submodule.span K G
  have hmax (μ : K) : Module.End.maxGenEigenspace T μ ≤ P := by
    intro x hx
    apply Submodule.subset_span
    refine ⟨μ, ?_⟩
    have hfin := Module.End.maxGenEigenspace_eq_genEigenspace_finrank T μ
    have hxfin : x ∈ Module.End.genEigenspace T μ (Module.finrank K V) := by
      rw [← hfin]
      exact hx
    simpa [generalizedEigenspace, Module.End.mem_genEigenspace_nat, dim,
      Module.End.one_eq_id] using hxfin
  have hall : (⊤ : Submodule K V) ≤ P := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
    exact iSup_le hmax
  have hP : P = ⊤ := top_unique hall
  unfold span
  change (↑P : Set V) = Set.univ
  rw [hP]
  rfl

/-- 长度 `m+1` 的 Jordan 链基：首向量是特征向量，后继向量依次映到前一向量。-/
def IsJordanChainBasis (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) : Prop :=
  IsBasis K b ∧ T (b 0) = μ • b 0 ∧
    ∀ j : Fin m, T (b j.succ) = μ • b j.succ + b j.castSucc

/-- 大小为 `m+1`、特征值为 `μ` 的 Jordan 块。-/
def jordanBlock (μ : K) (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if i = j then μ else if i.val + 1 = j.val then 1 else 0

/-- Jordan 块是上三角矩阵。非零的非对角元只可能位于紧邻主对角线的上方。-/
theorem jordanBlock_isUpperTriangular (μ : K) (m : ℕ) :
    (jordanBlock μ m).IsUpperTriangular := by
  intro i j hji
  change j.val < i.val at hji
  simp only [jordanBlock]
  split
  · next hij => subst i; exact (lt_irrefl _ hji).elim
  · split
    · next hsucc => omega
    · rfl

/-- **Jordan 块的特征多项式**：大小为 `m+1`、特征值为 `μ` 的 Jordan 块满足
`χ(X)=(X-μ)^(m+1)`。因此单个块只贡献一个特征值，其代数重数等于块大小。-/
theorem charpoly_jordanBlock (μ : K) (m : ℕ) :
    (jordanBlock μ m).charpoly =
      (Polynomial.X - Polynomial.C μ) ^ (m + 1) := by
  rw [Matrix.charpoly_of_isUpperTriangular _ (jordanBlock_isUpperTriangular μ m)]
  simp [jordanBlock]

/-- Jordan 链基下算子的矩阵就是相应 Jordan 块。-/
theorem operatorMatrix_eq_jordanBlock (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    operatorMatrix b hb.1 T = jordanBlock μ m := by
  classical
  let B := Module.Basis.mk hb.1.1 (by simpa [hb.1.2])
  have hB (j : Fin (m + 1)) : B j = b j := by simp [B]
  change LinearMap.toMatrix B B T = jordanBlock μ m
  ext i j
  refine Fin.cases ?_ (fun q => ?_) j
  · rw [LinearMap.toMatrix_apply]
    rw [show T (B 0) = μ • B 0 by simpa [hB] using hb.2.1]
    by_cases hi : i = 0
    · subst i
      simp [jordanBlock]
    · simp [jordanBlock, Finsupp.single_apply, hi]
  · rw [LinearMap.toMatrix_apply]
    rw [show T (B q.succ) = μ • B q.succ + B q.castSucc by
      simpa [hB] using hb.2.2 q]
    by_cases hsucc : i = q.succ
    · subst i
      simp [jordanBlock, Finsupp.single_apply, Fin.ext_iff]
    · by_cases hprev : i = q.castSucc
      · subst i
        simp [jordanBlock, Finsupp.single_apply, Fin.ext_iff]
      · have hval : i.val ≠ q.val := by
          intro h
          apply hprev
          exact Fin.ext h
        simp [jordanBlock, Finsupp.single_apply, hsucc, hprev, hval]

/-- 若整个有限维空间由一条长度 `m+1`、属于 `μ` 的 Jordan 链构成，则算子的
特征多项式为 `(X-μ)^(m+1)`。

证明先把算子写成该链基下的 Jordan 块，再使用矩阵表示不改变特征多项式。-/
theorem characteristicPolynomial_eq_pow_of_jordanChainBasis
    [IsFiniteDimensional K V] (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    Diagonalization.characteristicPolynomial T =
      (Polynomial.X - Polynomial.C μ) ^ (m + 1) := by
  classical
  let B := Module.Basis.mk hb.1.1 (by simpa [hb.1.2])
  calc
    Diagonalization.characteristicPolynomial T =
        (Coordinates.operatorMatrix b hb.1 T).charpoly := by
      symm
      simpa [Diagonalization.characteristicPolynomial, Coordinates.operatorMatrix, B] using
        (LinearMap.charpoly_toMatrix T B)
    _ = (jordanBlock μ m).charpoly := by
      rw [operatorMatrix_eq_jordanBlock T μ b hb]
    _ = (Polynomial.X - Polynomial.C μ) ^ (m + 1) := charpoly_jordanBlock μ m

/-- Jordan 链中的第 `j` 个向量被 `(T-μI)^(j+1)` 湮灭。-/
theorem jordanChain_power_annihilates (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) (j : Fin (m + 1)) :
    ((T - μ • (LinearMap.id : V →ₗ[K] V)) ^ (j.val + 1)) (b j) = 0 := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  have hzero : A (b 0) = 0 := by
    simp [A, LinearMap.sub_apply, hb.2.1]
  have hshift (q : Fin m) : A (b q.succ) = b q.castSucc := by
    simp [A, LinearMap.sub_apply, hb.2.2 q]
  refine Fin.induction ?_ (fun q ih => ?_) j
  · simpa [A] using hzero
  · change (A ^ (q.val + 1 + 1)) (b q.succ) = 0
    rw [pow_succ, Module.End.mul_apply, hshift q]
    exact ih

/-! ## Jordan 链与 Jordan 链基的接口分离 -/

/-- 长度 `m+1`、属于特征值 `μ` 的 Jordan 链。

链首是非零特征向量；每个后继向量经 `T-μI` 映到前一个向量。这里不要求链已经
张成整个空间，因此该定义可以用于后续从局部链组装 Jordan 基。-/
def IsJordanChain (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) : Prop :=
  b 0 ≠ 0 ∧ T (b 0) = μ • b 0 ∧
    ∀ j : Fin m, T (b j.succ) = μ • b j.succ + b j.castSucc

/-- **Jordan 链族基**：有限条 Jordan 链合在一起构成全空间的一组基。

`r` 是链的条数，`μ i` 是第 `i` 条链的特征值，`length i + 1` 是该链包含的向量
数。以依赖配对 `(i,j)` 编号所有链向量后，第一项要求它们共同构成全空间基；第二项
逐条记录 Jordan 链递推关系。该教材接口不预设矩阵，也不暴露内部子空间结构。-/
def IsJordanBasisFamily (T : V →ₗ[K] V) (r : ℕ)
    (μ : Fin r → K) (length : Fin r → ℕ)
    (b : (i : Fin r) → Fin (length i + 1) → V) : Prop :=
  IsBasis K (fun p : Σ i : Fin r, Fin (length i + 1) => b p.1 p.2) ∧
    ∀ i : Fin r, IsJordanChain T (μ i) (b i)

/-- 任意 Jordan 链中的第 `j` 个向量被 `(T-μI)^(j+1)` 湮灭。

与前面的链基版本不同，这里只假设局部 Jordan 链关系，不要求这些向量已经张成整个
空间。这是从局部链证明线性无关并最终组装 Jordan 基所需的形式。-/
theorem jordanChain_power_annihilates_general (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChain T μ b) (j : Fin (m + 1)) :
    ((T - μ • (LinearMap.id : V →ₗ[K] V)) ^ (j.val + 1)) (b j) = 0 := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  have hzero : A (b 0) = 0 := by
    simp [A, LinearMap.sub_apply, hb.2.1]
  have hshift (q : Fin m) : A (b q.succ) = b q.castSucc := by
    simp [A, LinearMap.sub_apply, hb.2.2 q]
  refine Fin.induction ?_ (fun q ih => ?_) j
  · simpa [A] using hzero
  · change (A ^ (q.val + 1 + 1)) (b q.succ) = 0
    rw [pow_succ, Module.End.mul_apply, hshift q]
    exact ih

/-- 删除 Jordan 链的最后一个向量，仍得到 Jordan 链。-/
theorem jordanChain_init (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 2) → V) (hb : IsJordanChain T μ b) :
    IsJordanChain T μ (fun i : Fin (m + 1) => b i.castSucc) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hb.1
  · simpa using hb.2.1
  · intro j
    simpa [Fin.ext_iff] using hb.2.2 j.castSucc

/-- **Jordan 链线性无关**：任意非零 Jordan 链中的向量线性无关。

证明对链长归纳。对一条线性关系施加 `A=T-μI`：链首项被杀掉，其余项整体向前
移动一格。由短一阶链的归纳假设，所有后继项系数均为零；原关系便只剩链首项，
再由链首非零得到首系数也为零。-/
theorem jordanChain_linearIndependent (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChain T μ b) :
    IsLinearIndependent K b := by
  unfold IsLinearIndependent
  induction m with
  | zero =>
      rw [Fintype.linearIndependent_iff]
      intro c hsum i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hsmul : c 0 • b 0 = 0 := by simpa using hsum
      exact (smul_eq_zero.mp hsmul).resolve_right hb.1
  | succ m ih =>
      let binit : Fin (m + 1) → V := fun i => b i.castSucc
      have hbinit : IsJordanChain T μ binit := jordanChain_init T μ b hb
      have hli : LinearIndependent K binit := ih binit hbinit
      rw [Fintype.linearIndependent_iff]
      intro c hsum
      let A := T - μ • (LinearMap.id : V →ₗ[K] V)
      have hzero : A (b 0) = 0 := by
        simp [A, LinearMap.sub_apply, hb.2.1]
      have hshift (j : Fin (m + 1)) : A (b j.succ) = b j.castSucc := by
        simp [A, LinearMap.sub_apply, hb.2.2 j]
      have hshift0 : A (b 1) = b 0 := by simpa using hshift 0
      have hA := congrArg A hsum
      have htail : ∑ j : Fin (m + 1), c j.succ • binit j = 0 := by
        simpa [Fin.sum_univ_succ, map_sum, map_smul, hzero, hshift, hshift0, binit] using hA
      have hcoeff : ∀ j : Fin (m + 1), c j.succ = 0 :=
        (Fintype.linearIndependent_iff.mp hli) (fun j => c j.succ) htail
      intro i
      refine Fin.cases ?_ (fun j => hcoeff j) i
      have hfirst : c 0 • b 0 = 0 := by
        simpa [Fin.sum_univ_succ, hcoeff] using hsum
      exact (smul_eq_zero.mp hfirst).resolve_right hb.1

/-- **链顶下降公式**：长度 `m+1` 的 Jordan 链顶经 `m` 次 `T-μI` 恰好降到链首。-/
theorem jordanChain_power_top_eq_first (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChain T μ b) :
    ((T - μ • (LinearMap.id : V →ₗ[K] V)) ^ m) (b (Fin.last m)) = b 0 := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  induction m with
  | zero => simp
  | succ m ih =>
      let binit : Fin (m + 1) → V := fun i => b i.castSucc
      have hbinit : IsJordanChain T μ binit := jordanChain_init T μ b hb
      have hshift : A (b (Fin.last (m + 1))) = b (Fin.last m).castSucc := by
        have h := hb.2.2 (Fin.last m)
        have hlast : (Fin.last m).succ = Fin.last (m + 1) := Fin.ext rfl
        change T (b (Fin.last (m + 1))) - μ • b (Fin.last (m + 1)) = _
        rw [← hlast, h]
        abel
      change (A ^ (m + 1)) (b (Fin.last (m + 1))) = b 0
      rw [pow_succ, Module.End.mul_apply, hshift]
      simpa [binit] using ih binit hbinit

/-- 因链首非零，长度 `m+1` 的 Jordan 链保证 `(T-μI)^m` 还不是零算子。-/
theorem jordanChain_shifted_power_ne_zero (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChain T μ b) :
    (T - μ • (LinearMap.id : V →ₗ[K] V)) ^ m ≠ 0 := by
  intro hzero
  have happ := congrArg (fun A : V →ₗ[K] V => A (b (Fin.last m))) hzero
  rw [jordanChain_power_top_eq_first T μ b hb] at happ
  exact hb.1 (by simpa using happ)

/-- 若一条长度 `m+1` 的 Jordan 链已经是全空间基，则 `(T-μI)^(m+1)` 是零算子。-/
theorem jordanChainBasis_shifted_power_eq_zero (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    (T - μ • (LinearMap.id : V →ₗ[K] V)) ^ (m + 1) = 0 := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  classical
  let B := Module.Basis.mk hb.1.1 (by simpa [hb.1.2])
  have hB (j : Fin (m + 1)) : B j = b j := by simp [B]
  apply B.ext
  intro j
  rw [LinearMap.zero_apply, hB]
  have hj := jordanChain_power_annihilates T μ b hb j
  have hle : j.val + 1 ≤ m + 1 := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  change (A ^ (m + 1)) (b j) = 0
  rw [hd, add_comm, pow_add, Module.End.mul_apply, hj, map_zero]

/-- Jordan 链基首先是一条 Jordan 链。链首非零由基的线性无关性保证。-/
theorem jordanChain_of_chainBasis (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    IsJordanChain T μ b := by
  exact ⟨LinearIndependent.ne_zero 0 hb.1.1, hb.2.1, hb.2.2⟩

/-- Jordan 链基中的向量线性无关。-/
theorem jordanChainBasis_linearIndependent (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    IsLinearIndependent K b := by
  exact hb.1.1

/-- Jordan 链基张成整个空间。-/
theorem jordanChainBasis_spans (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    span K (Set.range b) = Set.univ := by
  unfold span
  rw [hb.1.2]
  rfl

/-- Jordan 链基等价于“既是基又是一条 Jordan 链”。

这个拆分把局部链构造与全空间张成条件分离，避免后续链基存在性证明循环使用
“已经是一组基”的过强前提。-/
theorem jordanChainBasis_iff (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) :
    IsJordanChainBasis T μ b ↔ IsBasis K b ∧ IsJordanChain T μ b := by
  constructor
  · intro hb
    exact ⟨hb.1, jordanChain_of_chainBasis T μ b hb⟩
  · rintro ⟨hb, _hzero, hfirst, hsucc⟩
    exact ⟨hb, hfirst, hsucc⟩

/-! ## 单 Jordan 块的最小多项式 -/

/-- **链顶的逐级下降公式**：从链顶开始施加 `i` 次 `T-μI`，得到逆序编号的
第 `i` 个链向量。特别地，`i=m` 时回到链首；这里给出的是此前链顶公式的逐次版本。-/
theorem jordanChain_power_top_eq_rev (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChain T μ b) (i : Fin (m + 1)) :
    ((T - μ • (LinearMap.id : V →ₗ[K] V)) ^ i.val) (b (Fin.last m)) = b i.rev := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  have hzero : A (b 0) = 0 := by
    simp [A, LinearMap.sub_apply, hb.2.1]
  have hshift (q : Fin m) : A (b q.succ) = b q.castSucc := by
    simp [A, LinearMap.sub_apply, hb.2.2 q]
  refine Fin.induction ?_ (fun q ih => ?_) i
  · simp
  · change (A ^ (q.val + 1)) (b (Fin.last m)) = b q.succ.rev
    rw [pow_succ', Module.End.mul_apply]
    have ihA : (A ^ q.val) (b (Fin.last m)) = b q.castSucc.rev := by
      simpa [A] using ih
    rw [ihA]
    have hleft : q.castSucc.rev = q.rev.succ := by
      apply Fin.ext
      simp [Fin.rev]
      omega
    have hright : q.succ.rev = q.rev.castSucc := by
      apply Fin.ext
      simp [Fin.rev]
    rw [hleft, hshift q.rev, hright]

/-- **循环向量给出的幂线性无关性**：若 `b` 是 Jordan 链，则
`1,(T-μI),…,(T-μI)^m` 作为线性算子线性无关。

证明只需把一条算子线性关系作用到链顶；由上一条下降公式，它立刻变成逆序 Jordan
链向量之间的线性关系，而 Jordan 链已经证明为线性无关。-/
theorem jordanChain_shifted_powers_linearIndependent
    (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChain T μ b) :
    LinearIndependent K
      (fun i : Fin (m + 1) ↦
        (T - μ • (LinearMap.id : V →ₗ[K] V)) ^ i.val) := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  have hli : LinearIndependent K (fun i : Fin (m + 1) ↦ b i.rev) :=
    (jordanChain_linearIndependent T μ b hb).comp _ Fin.rev_injective
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have happ := congrArg (fun F : V →ₗ[K] V => F (b (Fin.last m))) hc
  have hsum : ∑ i : Fin (m + 1), c i • b i.rev = 0 := by
    simpa [A, map_sum, jordanChain_power_top_eq_rev T μ b hb] using happ
  exact (Fintype.linearIndependent_iff.mp hli) c hsum

/-- **单 Jordan 块的最小多项式**：若整个空间由一条长度 `m+1` 的 `μ`-Jordan
链构成，则平移算子 `T-μI` 的最小多项式恰为 `X^(m+1)`。

上界来自链基保证的 `(T-μI)^(m+1)=0`；下界来自前一条结论中前 `m+1` 个算子幂
线性无关。因此幂次数不能再降低。-/
theorem minimalPolynomial_shifted_eq_pow [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    Diagonalization.minimalPolynomial (T - μ • (LinearMap.id : V →ₗ[K] V)) =
      Polynomial.X ^ (m + 1) := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  unfold Diagonalization.minimalPolynomial
  exact minpoly.eq_of_linearIndependent K A (Polynomial.monic_X_pow _)
    (by simpa [A] using jordanChainBasis_shifted_power_eq_zero T μ b hb)
    (m + 1) (by simp)
    (jordanChain_shifted_powers_linearIndependent T μ b
      (jordanChain_of_chainBasis T μ b hb))

/-- **线性算子最小多项式的标量平移公式**：给算子加上 `aI`，等价于在原最小
多项式中把变量替换为 `X-a`。

mathlib 的同名一般结论要求目标代数交换，不能用于通常并不交换的线性算子环。
这里利用标量恒等算子处于中心这一事实，直接重复最小多项式的最小次数论证：正向
代入 `X-a`，反向代入 `X+a`，两次平移互相抵消且保持多项式次数。-/
theorem minimalPolynomial_add_scalar_identity [IsFiniteDimensional K V]
    (A : V →ₗ[K] V) (a : K) :
    Diagonalization.minimalPolynomial
        (A + a • (LinearMap.id : V →ₗ[K] V)) =
      (Diagonalization.minimalPolynomial A).comp
        (Polynomial.X - Polynomial.C a) := by
  unfold Diagonalization.minimalPolynomial
  have hscalar : a • (LinearMap.id : V →ₗ[K] V) =
      algebraMap K (V →ₗ[K] V) a := by
    ext x
    simp
  rw [hscalar]
  have hA : IsIntegral K A := IsIntegral.of_finite K A
  refine (minpoly.unique K _ ((minpoly.monic hA).comp_X_sub_C a) ?_ fun q qmo hq => ?_).symm
  · simp [Polynomial.aeval_comp]
  · have hqA : Polynomial.aeval A (q.comp (Polynomial.X + Polynomial.C a)) = 0 := by
      simpa [Polynomial.aeval_comp] using hq
    have hmin := minpoly.min K A (qmo.comp_X_add_C a) hqA
    rw [Polynomial.degree_eq_natDegree qmo.ne_zero,
      Polynomial.degree_eq_natDegree ((minpoly.monic hA).comp_X_sub_C a).ne_zero,
      Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
    rwa [Polynomial.degree_eq_natDegree (minpoly.ne_zero hA),
      Polynomial.degree_eq_natDegree (qmo.comp_X_add_C a).ne_zero,
      Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one] at hmin

/-- **单 Jordan 块算子的最小多项式**：若整个空间由一条长度 `m+1`、属于 `μ`
的 Jordan 链构成，则原算子的最小多项式与特征多项式相同，均为
`(X-μ)^(m+1)`。

证明先把算子平移为幂零算子 `T-μI`，使用其最小多项式 `X^(m+1)`，再由上一条
标量平移公式把变量平移回来。-/
theorem minimalPolynomial_eq_pow_of_jordanChainBasis
    [IsFiniteDimensional K V] (T : V →ₗ[K] V) (μ : K) {m : ℕ}
    (b : Fin (m + 1) → V) (hb : IsJordanChainBasis T μ b) :
    Diagonalization.minimalPolynomial T =
      (Polynomial.X - Polynomial.C μ) ^ (m + 1) := by
  let A := T - μ • (LinearMap.id : V →ₗ[K] V)
  have htranslate := minimalPolynomial_add_scalar_identity A μ
  have hA := minimalPolynomial_shifted_eq_pow T μ b hb
  have hAT : A + μ • (LinearMap.id : V →ₗ[K] V) = T := by
    simp [A]
  rw [hAT, hA] at htranslate
  simpa using htranslate

/-! ## 幂零算子的链分解前置 -/

/-- **有限维幂零指数上界**：有限维空间上的幂零算子至多经过 `dim V` 次就成为
零算子。

证明使用核空间链稳定定理：某个幂已经为零时，其核是全空间；所有幂的核都包含在
`dim V` 次幂的核中，故后者也只能是全空间。-/
theorem nilpotent_power_dim_eq_zero [IsFiniteDimensional K V]
    (N : V →ₗ[K] V) (hN : IsNilpotent N) : N ^ (dim K V) = 0 := by
  obtain ⟨n, hn⟩ := hN
  have hker_n : LinearMap.ker (N ^ n) = ⊤ := by
    rw [hn]
    simp
  have hle := Module.End.ker_pow_le_ker_pow_finrank N n
  rw [hker_n] at hle
  have hker_dim : LinearMap.ker (N ^ (dim K V)) = ⊤ := top_unique hle
  exact LinearMap.ker_eq_top.mp hker_dim

/-- **幂零算子有非零核向量**：在非平凡有限维空间中，任意幂零算子的核都包含
非零向量。

否则算子便是单射，继而它的所有幂都是单射；但 `dim V` 次幂已经是零算子，零算子
在非平凡空间上不可能单射。这个核向量将作为后续构造 Jordan 链的链首。-/
theorem nilpotent_exists_nonzero_kernel_vector
    [IsFiniteDimensional K V] [Nontrivial V]
    (N : V →ₗ[K] V) (hN : IsNilpotent N) : ∃ v : V, v ≠ 0 ∧ N v = 0 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective N := by
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hx
      by_contra hx0
      exact (h x hx0) hx
    · intro hx
      simp [hx]
  have hinj_pow : ∀ n : ℕ, Function.Injective (N ^ n) := by
    intro n
    induction n with
    | zero =>
        intro x y hxy
        simpa using hxy
    | succ n ih =>
        rw [pow_succ, Module.End.coe_mul]
        exact ih.comp hinj
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hzero := nilpotent_power_dim_eq_zero N hN
  apply hv
  apply hinj_pow (dim K V)
  rw [hzero]
  simp

/-- **精确幂零指数存在**：非平凡空间上的幂零算子存在唯一的首次归零次数 `m+1`；
换言之，`N^(m+1)=0`，而前一次幂 `N^m` 仍非零。

这里用自然数良序直接取满足 `N^k=0` 的最小 `k`。非平凡性排除 `k=0`，因为
零次幂是恒等算子。-/
theorem nilpotent_exact_index_exists [Nontrivial V]
    (N : V →ₗ[K] V) (hN : IsNilpotent N) :
    ∃ m : ℕ, N ^ (m + 1) = 0 ∧ N ^ m ≠ 0 := by
  classical
  let k := Nat.find hN
  have hkzero : N ^ k = 0 := Nat.find_spec hN
  have hkne : k ≠ 0 := by
    intro hk
    have hone : (1 : V →ₗ[K] V) = 0 := by
      simpa [hk] using hkzero
    exact one_ne_zero hone
  have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
  let m := k - 1
  have hmk : m + 1 = k := by
    simp [m, Nat.sub_add_cancel hkpos]
  refine ⟨m, hmk ▸ hkzero, ?_⟩
  exact Nat.find_min hN (by omega)

/-- **由精确幂零指数构造 Jordan 链**：若 `N^(m+1)=0` 而 `N^m≠0`，则存在
一条长度 `m+1`、特征值为零的 Jordan 链。

从某个满足 `N^m v≠0` 的向量 `v` 出发，按逆序定义
`b_i=N^(m-i)v`。链首非零，下一次作用被 `N^(m+1)=0` 杀掉；其余链关系只是幂
指数下降一格。-/
theorem jordanChain_exists_of_exact_nilpotency_index
    (N : V →ₗ[K] V) {m : ℕ}
    (hzero : N ^ (m + 1) = 0) (hne : N ^ m ≠ 0) :
    ∃ b : Fin (m + 1) → V, IsJordanChain N 0 b := by
  rw [DFunLike.ne_iff] at hne
  obtain ⟨v, hv⟩ := hne
  have hv' : (N ^ m) v ≠ 0 := by simpa using hv
  let b : Fin (m + 1) → V := fun i => (N ^ (m - i.val)) v
  refine ⟨b, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [b] using hv'
  · have hz := congrArg (fun F : V →ₗ[K] V => F v) hzero
    simpa [b, pow_succ', Module.End.mul_apply] using hz
  · intro j
    have harith : m - j.val = (m - (j.val + 1)) + 1 := by omega
    change N ((N ^ (m - (j.val + 1))) v) =
      0 • (N ^ (m - (j.val + 1))) v + (N ^ (m - j.val)) v
    rw [zero_smul, zero_add, harith, pow_succ', Module.End.mul_apply]

/-- **幂零算子的最长 Jordan 链**：非平凡空间上的幂零算子具有一条长度恰等于
其幂零指数的 Jordan 链。

这条链不一定已经张成全空间；它是后续取不变补空间并递归分解其余 Jordan 块的
第一条链。-/
theorem nilpotent_exists_maximal_jordanChain [Nontrivial V]
    (N : V →ₗ[K] V) (hN : IsNilpotent N) :
    ∃ (m : ℕ) (b : Fin (m + 1) → V),
      IsJordanChain N 0 b ∧ N ^ (m + 1) = 0 ∧ N ^ m ≠ 0 := by
  obtain ⟨m, hzero, hne⟩ := nilpotent_exact_index_exists N hN
  obtain ⟨b, hb⟩ := jordanChain_exists_of_exact_nilpotency_index N hzero hne
  exact ⟨m, b, hb, hzero, hne⟩

/-- **幂零指数的维数界**：若 `m+1` 是幂零算子的首次归零次数，则
`m+1 ≤ dim V`。

达到该指数的向量生成一条长度 `m+1` 的 Jordan 链，而 Jordan 链线性无关；有限维
空间中的线性无关组不可能含有超过空间维数的向量。-/
theorem nilpotency_index_le_dim [IsFiniteDimensional K V]
    (N : V →ₗ[K] V) {m : ℕ}
    (hzero : N ^ (m + 1) = 0) (hne : N ^ m ≠ 0) :
    m + 1 ≤ dim K V := by
  obtain ⟨b, hb⟩ := jordanChain_exists_of_exact_nilpotency_index N hzero hne
  have hli := jordanChain_linearIndependent N 0 b hb
  simpa using card_le_dim_of_linearIndependent hli

end SandronesLibrary.LinearAlgebra.Jordan
