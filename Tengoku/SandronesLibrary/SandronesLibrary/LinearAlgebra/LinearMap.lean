/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology
open scoped Filter Topology

/-!
# LinearAlgebra / LinearMap —— 线性映射 / 矩阵 / 秩（线性代数第一学期 L2）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **linear-algebra.maps.basic**（单射与核、满射与像、线性同构保持维数）。
* **linear-algebra.maps.first-isomorphism**（第一同构定理 `V/ker f ≃ im f`）。
* **linear-algebra.maps.rank**（线性映射的秩与零度）。
* **linear-algebra.maps.rank-nullity**（秩-零度定理：rank f + nullity f = dim V）。
* **linear-algebra.maps.matrix-rank**（矩阵的秩 = 列向量张成子空间的维数）。
* **linear-algebra.maps.rank-mul**（矩阵乘法秩的界：rank(AB) ≤ min rank A rank B）。
* **linear-algebra.maps.matrix**（线性映射的矩阵表示）。

> **实现注记**：教材的"线性映射 f 的秩"（rank f = dim(im f)）在形式化层 =
> `Module.finrank K f.range`；"零度" = `Module.finrank K f.ker`。
> 词条与叙述层只用教材记号（rank、nullity、im、ker、dim），mathlib 名只作实现注记。
-/

namespace SandronesLibrary

open LinearAlgebra.VectorSpace

namespace LinearAlgebra.LinearMap

/-! ## 核、像与线性同构 -/

/-- 线性映射单射当且仅当其核是零子空间。-/
theorem injective_iff_kernel_trivial {K V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : Function.Injective f ↔ f.ker = ⊥ := by
  exact LinearMap.ker_eq_bot.symm

/-- 线性映射满射当且仅当其像是整个陪域。-/
theorem surjective_iff_image_whole {K V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : Function.Surjective f ↔ f.range = ⊤ := by
  exact LinearMap.range_eq_top.symm

/-- 有限维向量空间线性同构时维数相等。-/
theorem dim_eq_of_linearEquiv {K V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    [IsFiniteDimensional K V] [IsFiniteDimensional K W]
    (e : V ≃ₗ[K] W) : dim K V = dim K W := by
  exact LinearEquiv.finrank_eq e

/-- **线性映射第一同构定理**：定义域对核的商空间线性同构于映射的像空间。-/
noncomputable def firstIsomorphism {K V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : (V ⧸ f.ker) ≃ₗ[K] f.range :=
  f.quotKerEquivRange

/-- 线性映射的**秩**：像空间 im f 的维数。-/
noncomputable abbrev rank (K : Type*) {V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : ℕ :=
  Module.finrank K f.range

/-- 线性映射的**零度**（nullity）：核 ker f 的维数。-/
noncomputable abbrev nullity (K : Type*) {V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : ℕ :=
  Module.finrank K f.ker

/-- 定义域对核的商空间维数。底层商空间结构封装在该教材记号内部。-/
noncomputable abbrev quotientKernelDimension (K : Type*) {V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : ℕ :=
  Module.finrank K (V ⧸ f.ker)

/-- 第一同构定理的维数推论：`dim(V/ker f)=rank f`。-/
theorem quotientKer_dim_eq_rank {K V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [IsFiniteDimensional K V]
    [AddCommGroup W] [LinearSpace K W]
    (f : V →ₗ[K] W) : quotientKernelDimension K f = rank K f := by
  exact LinearEquiv.finrank_eq (firstIsomorphism f)

/-- **秩-零度定理**：线性映射 f: V → W 满足 rank f + nullity f = dim V。
  （像的维数加核的维数等于定义域维数。） 
> **Entry**: linear-algebra.maps.rank-nullity-/
theorem rank_add_nullity {K : Type*} {V W : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] [IsFiniteDimensional K V]
    [AddCommGroup W] [LinearSpace K W] (f : V →ₗ[K] W) :
    rank K f + nullity K f = dim K V := by
  unfold rank nullity LinearAlgebra.VectorSpace.dim
  exact LinearMap.finrank_range_add_finrank_ker f

/-- 矩阵列空间的维数。底层张成子空间结构封装在该教材记号内部。
> **Entry**: linear-algebra.maps.matrix-rank-/
noncomputable abbrev columnRank (K : Type*) {m n : Type*} [Field K]
    [Fintype m] [Fintype n] (A : Matrix m n K) : ℕ :=
  Module.finrank K (Submodule.span K (Set.range A.col))

/-- 矩阵的秩等于列空间的维数。-/
lemma matrix_rank_eq_columnRank {K : Type*} {m n : Type*} [Field K]
    [Fintype m] [Fintype n] (A : Matrix m n K) :
    A.rank = columnRank K A :=
  Matrix.rank_eq_finrank_span_cols A

/-- 矩阵乘法的秩的界：rank(A·B) ≤ min rank A rank B。
  （线性方程组解空间维数的又一来源。） 
> **Entry**: linear-algebra.maps.rank-mul-/
lemma rank_mul_le {K : Type*} {m n o : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype o] (A : Matrix m n K) (B : Matrix n o K) :
    (A * B).rank ≤ min A.rank B.rank :=
  Matrix.rank_mul_le A B

/-- **行秩 = 列秩**：矩阵的秩不因转置改变（行秩即 Aᵀ 的秩，等于 A 的列秩）。
  教材"秩 = 行秩 = 列秩"即由此给出。 
> **Entry**: linear-algebra.maps.row-rank-/
theorem rank_transpose_eq {K : Type*} {m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) : A.transpose.rank = A.rank :=
  Matrix.rank_transpose A

end LinearAlgebra.LinearMap

end SandronesLibrary
