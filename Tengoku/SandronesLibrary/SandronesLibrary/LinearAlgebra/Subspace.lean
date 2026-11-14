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
# LinearAlgebra / Subspace —— 子空间与生成（线性代数第一学期 L1 补充）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **linear-algebra.vector-space.subspace**（子空间：加法与数乘封闭）。
* **linear-algebra.vector-space.span**（生成子空间：s ⊆ span(s)、span 单调）。

> **语言说明**：本文件用教材语言——子空间是满足"加法与数乘封闭"的非空子集
> （`IsSubspace`），不用 mathlib 的 `Submodule` 结构类名。
-/

namespace SandronesLibrary

open LinearAlgebra.VectorSpace

namespace LinearAlgebra.VectorSpace

/-- **子空间**：V 的一个非空子集 W，对加法和数乘都封闭。
  （教材定义；mathlib 底层是 `Submodule`，这里用人话记号。）-/
def IsSubspace (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (W : Set V) : Prop :=
  W.Nonempty ∧ (∀ ⦃u⦄, u ∈ W → ∀ ⦃v⦄, v ∈ W → u + v ∈ W) ∧
    (∀ (c : K) ⦃v⦄, v ∈ W → c • v ∈ W)

/-- **子空间的加法封闭性**：u, v ∈ W ⟹ u + v ∈ W。 
> **Entry**: linear-algebra.vector-space.subspace
@isnad1 id=mem.3h5v.s6.093893f5dc24 from=translated src=- shape=4ec4686a vocab=927e4bbc
-/
theorem subspace_add_mem {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {W : Set V} (hW : IsSubspace K W)
    {u v : V} (hu : u ∈ W) (hv : v ∈ W) : u + v ∈ W :=
  hW.2.1 hu hv

/-- **子空间的数乘封闭性**：v ∈ W ⟹ c·v ∈ W。 
> **Entry**: linear-algebra.vector-space.subspace
@isnad1 id=mem.2h5v.s6.2ac33dbc9a67 from=translated src=- shape=f1e53e46 vocab=02340a17
-/
theorem subspace_smul_mem {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {W : Set V} (hW : IsSubspace K W)
    (c : K) {v : V} (hv : v ∈ W) : c • v ∈ W :=
  hW.2.2 c hv

/-- **子空间包含零向量**：子空间非空，故含 0。 
> **Entry**: linear-algebra.vector-space.subspace
@isnad1 id=mem.1h3v.s5.80eae090fd5f from=translated src=- shape=f9b12f65 vocab=1a243fdf
-/
theorem subspace_zero_mem {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {W : Set V} (hW : IsSubspace K W) :
    (0 : V) ∈ W := by
  rcases hW with ⟨⟨z, hz⟩, _hadd, _hsmul⟩
  have : (0 : K) • z = 0 := zero_smul K z
  have hz0 : (0 : K) • z ∈ W := _hsmul (0 : K) hz
  simpa [this] using hz0

/-- **生成子空间**（教材记号）：`span K s` 是集合 s 张成的子空间（作为 V 的子集）。-/
noncomputable def span (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
    (s : Set V) : Set V :=
  ↑(Submodule.span K s)

/-- **生成子空间包含原集合**：s ⊆ span(s)。 
> **Entry**: linear-algebra.vector-space.span
@isnad1 id=le.0h3v.s5.e9d2d6356506 from=translated src=- shape=59c3ec63 vocab=b2cb29d8
-/
theorem subset_span {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {s : Set V} : s ⊆ span K s := by
  intro x hx
  unfold span
  exact Submodule.subset_span hx

/-- **生成子空间的单调性**：s ⊆ t ⟹ span(s) ⊆ span(t)。 
> **Entry**: linear-algebra.vector-space.span
@isnad1 id=le.1h4v.s5.d6fe35dbf7b7 from=translated src=- shape=9ad97dc0 vocab=b2cb29d8
-/
theorem span_mono {K : Type*} {V : Type*} [Field K]
    [AddCommGroup V] [LinearSpace K V] {s t : Set V} (h : s ⊆ t) :
    span K s ⊆ span K t := by
  unfold span
  intro x hx
  exact (Submodule.span_mono h) hx

end LinearAlgebra.VectorSpace

end SandronesLibrary
