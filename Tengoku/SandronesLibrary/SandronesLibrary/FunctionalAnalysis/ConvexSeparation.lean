/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.NormingFunctional
import Tengoku.Seed.Analysis.LocallyConvex.Separation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 凸集的 Hahn–Banach 分离定理

连续线性泛函的水平集是仿射超平面。几何 Hahn–Banach 定理用这样的超平面分离互不相交的凸集。
本文件直接使用 Mathlib 的 `Convex`、`StrongDual` 和几何分离定理，并公开开凸邻域、两个开凸集、
闭凸集与外点三种教材层接口。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 含零开凸集与外点可由一个连续线性泛函按 `1` 这一水平严格分开。

> **Entry**: functional-analysis.convex.separation-/
theorem separate_open_convex_neighborhood {s : Set E} {x : E}
    (hzero : (0 : E) ∈ s) (hconv : Convex ℝ s) (hopen : IsOpen s) (hx : x ∉ s) :
    ∃ f : StrongDual ℝ E, f x = 1 ∧ ∀ y ∈ s, f y < 1 := by
  exact separate_convex_open_set hzero hconv hopen hx

/-- 两个不交的开凸集可由同一个水平严格分到两侧。-/
theorem separate_disjoint_open_convex {s t : Set E}
    (hsconv : Convex ℝ s) (hsopen : IsOpen s)
    (htconv : Convex ℝ t) (htopen : IsOpen t) (hdisj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (c : ℝ),
      (∀ x ∈ s, f x < c) ∧ ∀ y ∈ t, c < f y := by
  exact geometric_hahn_banach_open_open hsconv hsopen htconv htopen hdisj

/-- 闭凸集与其外一点可被严格分离。-/
theorem separate_closed_convex_point {s : Set E} {x : E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) (hx : x ∉ s) :
    ∃ (f : StrongDual ℝ E) (c : ℝ), (∀ y ∈ s, f y < c) ∧ c < f x := by
  exact geometric_hahn_banach_closed_point hconv hclosed hx

/-- 闭凸集恰是所有包含它的闭半空间之交。-/
theorem closedConvex_eq_iInter_halfSpaces {s : Set E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) :
    ⋂ f : StrongDual ℝ E, {x | ∃ y ∈ s, f x ≤ f y} = s := by
  exact iInter_halfSpaces_eq hconv hclosed

end SandronesLibrary.FunctionalAnalysis
