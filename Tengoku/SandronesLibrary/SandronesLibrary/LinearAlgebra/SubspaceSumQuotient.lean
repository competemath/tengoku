/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Subspace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / SubspaceSumQuotient —— 子空间和、直和与商空间维数

本文件使用集合形式的教材子空间 `IsSubspace`，补齐有限维线性代数中的三条标准主线：

* 子空间的和与交仍是子空间；
* `dim W + dim U = dim (W + U) + dim (W ∩ U)`，直和情形相交项为零；
* `dim (V/W) + dim W = dim V`。

公开签名不暴露 mathlib 的模或子模结构。`subspaceDim` 和 `quotientDim` 是教材层的
数值接口；底层商空间及有限维公式只在定义体和证明内部出现。

> **Entry**: linear-algebra.vector-space.sum-quotient
-/

namespace SandronesLibrary.LinearAlgebra.SubspaceTheory

open SandronesLibrary.LinearAlgebra.VectorSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

/-- 两个子空间的和：由一个来自 `W` 的向量与一个来自 `U` 的向量相加所得。-/
def subspaceSum (W U : Set V) : Set V := {x | ∃ w ∈ W, ∃ u ∈ U, w + u = x}

/-- 两个子空间的交。-/
def subspaceIntersection (W U : Set V) : Set V := W ∩ U

/-- 教材意义下子空间 `W` 的维数。-/
noncomputable def subspaceDim (K : Type*) {V : Type*} [Field K] [AddCommGroup V]
    [LinearSpace K V] (W : Set V) (hW : IsSubspace K W) : ℕ := by
  let S : Submodule K V :=
    { carrier := W
      zero_mem' := subspace_zero_mem hW
      add_mem' := by intro a b ha hb; exact hW.2.1 ha hb
      smul_mem' := by intro c x hx; exact hW.2.2 c hx }
  exact Module.finrank K S

/-- 商空间 `V/W` 的维数。-/
noncomputable def quotientDim (K : Type*) {V : Type*} [Field K] [AddCommGroup V]
    [LinearSpace K V] (W : Set V) (hW : IsSubspace K W) : ℕ := by
  let S : Submodule K V :=
    { carrier := W
      zero_mem' := subspace_zero_mem hW
      add_mem' := by intro a b ha hb; exact hW.2.1 ha hb
      smul_mem' := by intro c x hx; exact hW.2.2 c hx }
  exact Module.finrank K (V ⧸ S)

/-- `W` 与 `U` 的和是子空间。
@isnad1 id=issubspa.2h4v.s5.2303a8d45aaa from=translated src=- shape=188b375a vocab=edf74100
-/
theorem subspaceSum_isSubspace {W U : Set V} (hW : IsSubspace K W)
    (hU : IsSubspace K U) : IsSubspace K (subspaceSum W U) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, 0, subspace_zero_mem hW, 0, subspace_zero_mem hU, add_zero 0⟩
  · rintro x ⟨w₁, hw₁, u₁, hu₁, rfl⟩ y ⟨w₂, hw₂, u₂, hu₂, rfl⟩
    exact ⟨w₁ + w₂, hW.2.1 hw₁ hw₂, u₁ + u₂, hU.2.1 hu₁ hu₂, by abel⟩
  · rintro c x ⟨w, hw, u, hu, rfl⟩
    exact ⟨c • w, hW.2.2 c hw, c • u, hU.2.2 c hu, by simp [smul_add]⟩

/-- `W` 与 `U` 的交是子空间。
@isnad1 id=issubspa.2h4v.s5.e4bc5ae02793 from=translated src=- shape=188b375a vocab=9eb35b71
-/
theorem subspaceIntersection_isSubspace {W U : Set V} (hW : IsSubspace K W)
    (hU : IsSubspace K U) : IsSubspace K (subspaceIntersection W U) := by
  refine ⟨⟨0, subspace_zero_mem hW, subspace_zero_mem hU⟩, ?_, ?_⟩
  · rintro x ⟨hxW, hxU⟩ y ⟨hyW, hyU⟩
    exact ⟨hW.2.1 hxW hyW, hU.2.1 hxU hyU⟩
  · rintro c x ⟨hxW, hxU⟩
    exact ⟨hW.2.2 c hxW, hU.2.2 c hxU⟩

/-- 两个子空间直和，当且仅当它们的公共向量只有零向量。-/
def IsDirectSum (W U : Set V) : Prop := ∀ x, x ∈ W → x ∈ U → x = 0

/-- 子空间维数公式：`dim W + dim U = dim(W+U) + dim(W∩U)`。
@isnad1 id=eq.2h4v.s6.31a62aab0ef7 from=translated src=- shape=0a14cea6 vocab=56f46b1d
-/
theorem subspaceDim_add_subspaceDim {W U : Set V} (hW : IsSubspace K W)
    (hU : IsSubspace K U) [IsFiniteDimensional K V] :
    subspaceDim K W hW + subspaceDim K U hU =
      subspaceDim K (subspaceSum W U) (subspaceSum_isSubspace hW hU) +
        subspaceDim K (subspaceIntersection W U) (subspaceIntersection_isSubspace hW hU) := by
  let S : Submodule K V :=
    { carrier := W
      zero_mem' := subspace_zero_mem hW
      add_mem' := by intro a b ha hb; exact hW.2.1 ha hb
      smul_mem' := by intro c x hx; exact hW.2.2 c hx }
  let T : Submodule K V :=
    { carrier := U
      zero_mem' := subspace_zero_mem hU
      add_mem' := by intro a b ha hb; exact hU.2.1 ha hb
      smul_mem' := by intro c x hx; exact hU.2.2 c hx }
  let P : Submodule K V :=
    { carrier := subspaceSum W U
      zero_mem' := subspace_zero_mem (subspaceSum_isSubspace hW hU)
      add_mem' := by intro a b ha hb; exact (subspaceSum_isSubspace hW hU).2.1 ha hb
      smul_mem' := by intro c x hx; exact (subspaceSum_isSubspace hW hU).2.2 c hx }
  let Q : Submodule K V :=
    { carrier := subspaceIntersection W U
      zero_mem' := subspace_zero_mem (subspaceIntersection_isSubspace hW hU)
      add_mem' := by intro a b ha hb; exact (subspaceIntersection_isSubspace hW hU).2.1 ha hb
      smul_mem' := by intro c x hx; exact (subspaceIntersection_isSubspace hW hU).2.2 c hx }
  have hP : P = S ⊔ T := by
    ext x
    simp [P, S, T, subspaceSum, Submodule.mem_sup]
  have hQ : Q = S ⊓ T := by
    ext x
    simp [Q, S, T, subspaceIntersection]
  change Module.finrank K S + Module.finrank K T =
    Module.finrank K P + Module.finrank K Q
  rw [hP, hQ]
  exact (Submodule.finrank_sup_add_finrank_inf_eq S T).symm

/-- 直和的维数等于两个子空间维数之和。
@isnad1 id=eq.3h4v.s6.41d4eda619dd from=translated src=- shape=275526b3 vocab=d0b9f46d
-/
theorem subspaceDim_directSum {W U : Set V} (hW : IsSubspace K W)
    (hU : IsSubspace K U) [IsFiniteDimensional K V] (hdir : IsDirectSum W U) :
    subspaceDim K (subspaceSum W U) (subspaceSum_isSubspace hW hU) =
      subspaceDim K W hW + subspaceDim K U hU := by
  let Q : Submodule K V :=
    { carrier := subspaceIntersection W U
      zero_mem' := subspace_zero_mem (subspaceIntersection_isSubspace hW hU)
      add_mem' := by intro a b ha hb; exact (subspaceIntersection_isSubspace hW hU).2.1 ha hb
      smul_mem' := by intro c x hx; exact (subspaceIntersection_isSubspace hW hU).2.2 c hx }
  have hQ : Q = ⊥ := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ W ∩ U := hx
      simpa [hdir x hx'.1 hx'.2]
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      subst x
      exact subspace_zero_mem (subspaceIntersection_isSubspace hW hU)
  have hinter :
      subspaceDim K (subspaceIntersection W U) (subspaceIntersection_isSubspace hW hU) = 0 := by
    change Module.finrank K Q = 0
    rw [hQ]
    simp
  have hdim := subspaceDim_add_subspaceDim hW hU
  omega

/-- 商空间维数公式：`dim(V/W) + dim W = dim V`。
@isnad1 id=eq.1h3v.s6.2b6b00002d2f from=translated src=- shape=dfd2ef06 vocab=5d57bc72
-/
theorem quotientDim_add_subspaceDim (W : Set V) (hW : IsSubspace K W)
    [IsFiniteDimensional K V] :
    quotientDim K W hW + subspaceDim K W hW = dim K V := by
  let S : Submodule K V :=
    { carrier := W
      zero_mem' := subspace_zero_mem hW
      add_mem' := by intro a b ha hb; exact hW.2.1 ha hb
      smul_mem' := by intro c x hx; exact hW.2.2 c hx }
  change Module.finrank K (V ⧸ S) + Module.finrank K S = Module.finrank K V
  exact Submodule.finrank_quotient_add_finrank S

end SandronesLibrary.LinearAlgebra.SubspaceTheory
