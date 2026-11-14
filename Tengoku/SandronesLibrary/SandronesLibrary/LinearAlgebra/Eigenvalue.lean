/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.LinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology
open scoped Filter Topology

/-!
# LinearAlgebra / Eigenvalue —— 特征值 / 相似 / 对角化（线性代数第一学期 L4）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **linear-algebra.eigen.vector**（特征向量：T(x) = μ·x，x ≠ 0）。
* **linear-algebra.eigen.value**（特征值：存在非零特征向量 ⟺ 特征子空间非平凡）。
* **linear-algebra.eigen.spectrum**（谱：特征值属于谱）。
* **linear-algebra.eigen.charpoly**（特征多项式：对角阵特征多项式 = ∏(X−dᵢ)）。
* **linear-algebra.eigen.charpoly-root**（特征值是特征多项式根）。
* **linear-algebra.eigen.independent**（不同特征值对应特征向量线性无关）。
* **linear-algebra.eigen.similar-diagonal**（相似与对角化：可对角化记号、对角阵可对角化、可逆 ⟹ 左右逆）。
* ~~similar-charpoly~~（相似保持特征多项式）：需 charmatrix 乘积分布 + 矩阵可逆桥接，留待后续。

> **语言说明**：线性变换用 `T : V →ₗ[K] V`（LinearMap，本阶段内容）；
> 特征向量/值、特征子空间都用教材公式表达（不用 `Module.End`/`HasEigenvector` 结构类名）。
-/

namespace SandronesLibrary

open LinearAlgebra.VectorSpace

namespace LinearAlgebra.Eigenvalue

/-- **特征子空间**：属于特征值 μ 的全体特征向量加零向量。
  E_μ(T) = { x | T(x) = μ·x }。-/
def eigenspace (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (T : V →ₗ[K] V) (μ : K) : Set V :=
  { x | T x = μ • x }

/-- **特征向量**：x 是 T 的属于 μ 的特征向量，若 x ≠ 0 且 T(x) = μ·x。-/
def HasEigenvector (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (T : V →ₗ[K] V) (μ : K) (x : V) : Prop :=
  x ≠ 0 ∧ x ∈ eigenspace K T μ

/-- **特征值**：μ 是 T 的特征值，若存在非零向量 x 使 T(x) = μ·x。-/
def HasEigenvalue (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (T : V →ₗ[K] V) (μ : K) : Prop :=
  ∃ x ≠ 0, T x = μ • x

/-- **特征向量满足 T(x) = μ·x**：特征向量定义的第二条。 
> **Entry**: linear-algebra.eigen.vector
@isnad1 id=eq.1h5v.s8.667fba884fad from=translated src=- shape=ec832c09 vocab=9214091c
-/
theorem eigenvector_apply {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {T : V →ₗ[K] V} {μ : K} {x : V}
    (hx : HasEigenvector K T μ x) : T x = μ • x :=
  hx.2

/-- **特征值 ⟺ 存在非零特征向量**：由定义直得。 
> **Entry**: linear-algebra.eigen.value
@isnad1 id=iff.0h4v.s6.f178f04d214b from=translated src=- shape=5e26df66 vocab=7356c4af
-/
theorem eigenvalue_iff_exists_eigenvector {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {T : V →ₗ[K] V} {μ : K} :
    HasEigenvalue K T μ ↔ ∃ x, HasEigenvector K T μ x := by
  constructor
  · rintro ⟨x, hx0, hTx⟩
    exact ⟨x, hx0, hTx⟩
  · rintro ⟨x, hx0, hTx⟩
    exact ⟨x, hx0, hTx⟩

/-- **特征子空间非平凡 ⟺ 特征值**：E_μ(T) ≠ {0} 当且仅当 μ 是特征值。 
> **Entry**: linear-algebra.eigen.value
@isnad1 id=iff.0h4v.s6.6b8ca552f2c7 from=translated src=- shape=37cb2423 vocab=39a87540
-/
theorem eigenvalue_iff_eigenspace_nontrivial {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {T : V →ₗ[K] V} {μ : K} :
    HasEigenvalue K T μ ↔ ∃ x, x ∈ eigenspace K T μ ∧ x ≠ 0 := by
  constructor
  · rintro ⟨x, hx0, hTx⟩
    exact ⟨x, hTx, hx0⟩
  · rintro ⟨x, hx, hx0⟩
    exact ⟨x, hx0, hx⟩

/-- **谱**：T 的谱是全体特征值的集合。-/
def spectrum (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (T : V →ₗ[K] V) : Set K :=
  { μ | HasEigenvalue K T μ }

/-- **特征值属于谱**：μ 是特征值，则 μ ∈ spectrum(T)。 
> **Entry**: linear-algebra.eigen.spectrum
@isnad1 id=mem.1h4v.s6.c17da5cdd16a from=translated src=- shape=fb045852 vocab=137393e1
-/
theorem eigenvalue_mem_spectrum {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {T : V →ₗ[K] V} {μ : K}
    (hμ : HasEigenvalue K T μ) : μ ∈ spectrum K T :=
  hμ

/-- **特征多项式**：对角矩阵 diag(d₁,…,dₙ) 的特征多项式是 ∏ᵢ (X − dᵢ)。
  （对角元即特征值；这是"特征值是特征多项式根"的直接来源。） 
> **Entry**: linear-algebra.eigen.charpoly
@isnad1 id=eq.0h3v.s7.63deb843b6a7 from=translated src=- shape=b89bad6e vocab=b3f58c69
-/
theorem charpoly_diagonal {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (d : n → K) : (Matrix.diagonal d).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) :=
  Matrix.charpoly_diagonal d

/-- **特征多项式首一**：n 阶矩阵的特征多项式是首一的。 
> **Entry**: linear-algebra.eigen.charpoly
@isnad1 id=monic.0h3v.s5.6804dda122c2 from=translated src=- shape=cf402585 vocab=376f52ce
-/
theorem charpoly_monic {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (M : Matrix n n K) : M.charpoly.Monic :=
  M.charpoly_monic

/-- **不同特征值对应特征向量线性无关**：设 {μᵢ} 是一族（成对不同的）特征值，
  对每个 μᵢ 取一个属于它的特征向量 xᵢ，则 {xᵢ} 线性无关。 
> **Entry**: linear-algebra.eigen.independent
@isnad1 id=islinear.1h5v.s6.aa3d086acb93 from=translated src=- shape=8d77b779 vocab=4548630d
-/
theorem eigenvectors_linearIndependent {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {T : V →ₗ[K] V}
    (μs : Set K) (xs : ↑μs → V)
    (h_eigen : ∀ μ : ↑μs, HasEigenvector K T (↑μ) (xs μ)) :
    IsLinearIndependent K xs := by
  letI : Module K V := LinearSpace.toModule (K := K) (V := V)
  have h_eigen' : ∀ μ : ↑μs, Module.End.HasEigenvector T (↑μ) (xs μ) := by
    intro μ
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr (h_eigen μ).2, (h_eigen μ).1⟩
  unfold IsLinearIndependent
  exact Module.End.eigenvectors_linearIndependent T μs xs h_eigen'

/-- **可逆矩阵**（教材记号）：方阵 A 可逆，若 det A 是域中的非零元（可逆元）。
  （数学上 det A ≠ 0 ⟺ A 可逆。）-/
def IsInvertible {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : Prop :=
  IsUnit A.det

/-- **可对角化**（教材记号）：方阵 A 可对角化，若存在可逆阵 P 与对角阵 diag(d)，
  使 P⁻¹·A·P = diag(d)。-/
def IsDiagonalizable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : Prop :=
  ∃ (d : n → K) (P : Matrix n n K), IsUnit P.det ∧ P⁻¹ * A * P = Matrix.diagonal d

/-- **对角阵可对角化**：对角阵 diag(d) 取 P = 单位阵即满足定义。 
> **Entry**: linear-algebra.eigen.similar-diagonal
@isnad1 id=isdiagon.0h3v.s5.320b840cdd86 from=translated src=- shape=d9a720d5 vocab=1ad07970
-/
theorem diagonalizable_diagonal {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → K) : IsDiagonalizable (Matrix.diagonal d) := by
  unfold IsDiagonalizable
  refine ⟨d, 1, ?_, ?_⟩
  · simp
  · simp

/-- **可逆 ⟹ 左右逆**：若 det A 可逆（≠0），则 A⁻¹ 给出 A⁻¹·A = 1 与 A·A⁻¹ = 1。 
> **Entry**: linear-algebra.eigen.similar-diagonal
@isnad1 id=and.1h3v.s7.ab5e698def12 from=translated src=- shape=52287ff9 vocab=7cfe7671
-/
theorem invertible_mul_inv {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : IsUnit A.det) :
    A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul A h, Matrix.mul_nonsing_inv A h⟩

/-- **相似保持行列式（逐点特征多项式）**：若 P⁻¹·A·P = D（A 相似于 D，P 可逆），
  则对每个标量 c，det(c·1 − A) = det(c·1 − D)。
  这正是"相似保持特征多项式"（charpoly 即 det(X·1 − A)）的逐点形式；
  证明只用数矩阵的 det 乘性与可逆阵的左右逆，不引入多项式矩阵。 
> **Entry**: linear-algebra.eigen.similar-charpoly
@isnad1 id=eq.2h6v.s8.63ee55fa9ceb from=translated src=- shape=5ef4ff60 vocab=c8c2282f
-/
theorem similar_det {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A D P : Matrix n n K) (h : P⁻¹ * A * P = D) (hP : IsUnit P.det) :
    ∀ c : K, (c • (1 : Matrix n n K) - A).det = (c • (1 : Matrix n n K) - D).det := by
  intro c
  have hne : P.det ≠ 0 := (isUnit_iff_ne_zero.mp hP)
  have hdet_conj : ∀ N : Matrix n n K, (P⁻¹ * N * P).det = N.det := by
    intro N
    calc
      (P⁻¹ * N * P).det = (P⁻¹ * (N * P)).det := by rw [Matrix.mul_assoc]
      _ = P⁻¹.det * (N * P).det := by rw [Matrix.det_mul]
      _ = P⁻¹.det * (N.det * P.det) := by rw [Matrix.det_mul]
      _ = (P⁻¹.det * P.det) * N.det := by ring
      _ = 1 * N.det := by
        rw [Matrix.det_nonsing_inv]
        simp [hne]
      _ = N.det := by simp
  calc
    (c • 1 - A).det = (P⁻¹ * (c • 1 - A) * P).det := by
      exact (hdet_conj (c • 1 - A)).symm
    _ = (c • 1 - P⁻¹ * A * P).det := by
      congr 1
      have hcomm : P⁻¹ * (c • (1 : Matrix n n K)) * P = c • (1 : Matrix n n K) := by
        calc
          P⁻¹ * (c • 1) * P = P⁻¹ * (c • 1 * P) := by rw [Matrix.mul_assoc]
          _ = P⁻¹ * (P * (c • 1)) := by congr 1; exact (by
            rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul])
          _ = (P⁻¹ * P) * (c • 1) := by rw [Matrix.mul_assoc]
          _ = 1 * (c • 1) := by rw [Matrix.nonsing_inv_mul P hP]
          _ = c • 1 := by simp
      calc
        P⁻¹ * (c • 1 - A) * P = (P⁻¹ * (c • 1) - P⁻¹ * A) * P := by rw [Matrix.mul_sub]
        _ = P⁻¹ * (c • 1) * P - P⁻¹ * A * P := by rw [sub_mul]
        _ = c • 1 - P⁻¹ * A * P := by rw [hcomm]
    _ = (c • 1 - D).det := by rw [h]

/-- **矩阵的特征值**（教材记号）：μ 是方阵 A 的特征值，若存在非零向量 x 使 A·x = μ·x。
  （等价于线性变换 `A.toLin'` 以 μ 为特征值。）-/
def MatrixHasEigenvalue {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (μ : K) : Prop :=
  ∃ x : n → K, x ≠ 0 ∧ A.mulVec x = μ • x

/-- 教材式矩阵特征值定义与 mathlib 特征空间定义等价；仅供本文件证明调用。-/
private theorem matrixHasEigenvalue_iff_mathlib {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (μ : K) :
    MatrixHasEigenvalue A μ ↔ Module.End.HasEigenvalue A.toLin' μ := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    have hxmem : x ∈ Module.End.eigenspace A.toLin' μ :=
      Module.End.mem_eigenspace_iff.mpr (by simpa using hx)
    rw [hbot] at hxmem
    exact hx0 (by simpa using hxmem)
  · intro h
    rw [Module.End.hasEigenvalue_iff] at h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact ⟨x, hx0, by simpa using Module.End.mem_eigenspace_iff.mp hx⟩

/-- **特征值是特征多项式的根**：μ 是方阵 A 的特征值 ⟺ μ 是 A 的特征多项式 charpoly 的根。
  教材核心：charpoly = det(X·1 − A)，其根恰为特征值。 
> **Entry**: linear-algebra.eigen.charpoly-root
@isnad1 id=iff.0h4v.s5.d446686537e6 from=translated src=- shape=d2da196c vocab=776b7083
-/
theorem eigenvalue_iff_isRoot_charpoly {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (μ : K) : MatrixHasEigenvalue A μ ↔ A.charpoly.IsRoot μ := by
  rw [matrixHasEigenvalue_iff_mathlib]
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly (f := A.toLin') μ]
  rw [Matrix.charpoly_toLin']

end LinearAlgebra.Eigenvalue

end SandronesLibrary
