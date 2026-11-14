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

> **Entry**: functional-analysis.convex.separation
@isnad1 id=ex.4h3v.s8.3f84507c1209 from=translated src=- shape=71220339 vocab=cbdca4fb
-/
theorem separate_open_convex_neighborhood {s : Set E} {x : E}
    (hzero : (0 : E) ∈ s) (hconv : Convex ℝ s) (hopen : IsOpen s) (hx : x ∉ s) :
    ∃ f : StrongDual ℝ E, f x = 1 ∧ ∀ y ∈ s, f y < 1 := by
  exact separate_convex_open_set hzero hconv hopen hx

/-- 两个不交的开凸集可由同一个水平严格分到两侧。
@isnad1 id=ex.5h3v.s8.75a0cd1ba827 from=translated src=- shape=9017f52f vocab=dd23dba3
-/
theorem separate_disjoint_open_convex {s t : Set E}
    (hsconv : Convex ℝ s) (hsopen : IsOpen s)
    (htconv : Convex ℝ t) (htopen : IsOpen t) (hdisj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (c : ℝ),
      (∀ x ∈ s, f x < c) ∧ ∀ y ∈ t, c < f y := by
  exact geometric_hahn_banach_open_open hsconv hsopen htconv htopen hdisj

/-- 闭凸集与其外一点可被严格分离。
@isnad1 id=ex.3h3v.s8.3bce49023b55 from=translated src=- shape=1e546b97 vocab=75d2faf0
-/
theorem separate_closed_convex_point {s : Set E} {x : E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) (hx : x ∉ s) :
    ∃ (f : StrongDual ℝ E) (c : ℝ), (∀ y ∈ s, f y < c) ∧ c < f x := by
  exact geometric_hahn_banach_closed_point hconv hclosed hx

/-- 闭凸集恰是所有包含它的闭半空间之交。
@isnad1 id=eq.2h2v.s8.86374d49d980 from=translated src=- shape=69bfb68b vocab=53d333c1
-/
theorem closedConvex_eq_iInter_halfSpaces {s : Set E}
    (hconv : Convex ℝ s) (hclosed : IsClosed s) :
    ⋂ f : StrongDual ℝ E, {x | ∃ y ∈ s, f x ≤ f y} = s := by
  exact iInter_halfSpaces_eq hconv hclosed

end SandronesLibrary.FunctionalAnalysis
