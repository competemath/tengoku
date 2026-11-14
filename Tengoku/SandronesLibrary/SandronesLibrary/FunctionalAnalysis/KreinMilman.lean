/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Analysis.Convex.KreinMilman

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Krein--Milman 的教材定义链

本文件不重建 face、极点或闭凸包，也不重证 Mathlib 的 Krein--Milman 定理。它把 Salamon
Definition 3.5.1 中 face 的额外非空、凸性条件与 Mathlib `IsExtreme` 组合，并给出极点、singleton
face、闭凸包结论之间的教材组装。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {K F : Set E} {x : E}

/-- Salamon Definition 3.5.1 的 face 条件展开。

教材中的 face 还要求 `F` 非空且凸；Mathlib 的 `IsExtreme ℝ K F` 只承载“开线段内点落入 `F`
则两端点落入 `F`”的极性条件，因此正式教材承载是三项合取，而不是另建一个同义谓词。

> **Entry**: functional-analysis.krein-milman
@isnad1 id=iff.0h3v.s8.24b5ab1ab252 from=translated src=- shape=4f0b51eb vocab=2008c706
-/
theorem textbookFace_iff_nonempty_convex_isExtreme :
    F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ K F ↔
      F.Nonempty ∧ Convex ℝ F ∧ F ⊆ K ∧
        ∀ ⦃x₀⦄, x₀ ∈ K → ∀ ⦃x₁⦄, x₁ ∈ K →
          ∀ ⦃z⦄, z ∈ F → z ∈ openSegment ℝ x₀ x₁ → x₀ ∈ F ∧ x₁ ∈ F := by
  constructor
  · rintro ⟨hne, hconv, hface⟩
    refine ⟨hne, hconv, hface.subset, ?_⟩
    intro x₀ hx₀ x₁ hx₁ z hz hseg
    exact ⟨hface.left_mem_of_mem_openSegment hx₀ hx₁ hz hseg,
      hface.right_mem_of_mem_openSegment hx₀ hx₁ hz hseg⟩
  · rintro ⟨hne, hconv, hsub, hface⟩
    exact ⟨hne, hconv,
      ⟨hsub, fun {x₀} hx₀ {x₁} hx₁ {z} hz hseg ↦ (hface hx₀ hx₁ hz hseg).1⟩⟩

/-- Salamon Definition 3.5.1 的 extremal point 展开：`x` 属于 `K`，且任何以 `x` 为严格内点、
端点属于 `K` 的线段都是平凡线段。

> **Entry**: functional-analysis.krein-milman
@isnad1 id=iff.0h3v.s7.5b54e772d2bb from=translated src=- shape=8762673f vocab=3decf66f
-/
theorem mem_extremePoints_iff_textbook :
    x ∈ K.extremePoints ℝ ↔
      x ∈ K ∧ ∀ x₀ ∈ K, ∀ x₁ ∈ K,
        x ∈ openSegment ℝ x₀ x₁ → x₀ = x ∧ x₁ = x :=
  mem_extremePoints

/-- 一个点是 `K` 的极点，当且仅当其 singleton 是 Mathlib 意义下的 extreme subset。这是教材
“extremal point 等价于 singleton face”的极性部分；完整 face 还需另加非空与凸性。

> **Entry**: functional-analysis.krein-milman
@isnad1 id=iff.0h3v.s7.19ac446842a6 from=translated src=- shape=a877b746 vocab=5f6ad4f8
-/
theorem singleton_isExtreme_iff_mem_extremePoints :
    IsExtreme ℝ K {x} ↔ x ∈ K.extremePoints ℝ :=
  isExtreme_singleton

section Topology

variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Salamon Theorem 3.5.2，以 Mathlib `closedConvexHull` 语言组装：紧凸集等于其极点的闭凸包。
证明直接复用 Mathlib Krein--Milman 最终定理，不建立平行最终接口或重复证明链。

> **Entry**: functional-analysis.krein-milman
@isnad1 id=eq.2h2v.s8.d3219aea4f25 from=translated src=- shape=4fb32577 vocab=d6aa2f69
-/
theorem closedConvexHull_extremePoints_eq (hKcpt : IsCompact K) (hKconv : Convex ℝ K) :
    closedConvexHull ℝ (K.extremePoints ℝ) = K := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact closure_convexHull_extremePoints hKcpt hKconv

/-- Salamon Theorem 3.5.2 的存在性推论：非空紧凸集具有极点。Mathlib 的底层存在性引理事实上
不需要凸性；这里保留教材环境，并显式复用该更强引理。

> **Entry**: functional-analysis.krein-milman
@isnad1 id=ex.3h2v.s7.9adc776e93d3 from=translated src=- shape=f2fc5483 vocab=ae87970a
-/
theorem exists_extremePoint_of_nonempty_compact_convex
    (hKne : K.Nonempty) (hKcpt : IsCompact K) (_hKconv : Convex ℝ K) :
    ∃ x, x ∈ K.extremePoints ℝ :=
  hKcpt.extremePoints_nonempty hKne

end Topology

end SandronesLibrary.FunctionalAnalysis
