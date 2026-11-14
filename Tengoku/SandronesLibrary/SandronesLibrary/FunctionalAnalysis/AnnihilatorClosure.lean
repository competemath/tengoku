/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.ConvexSeparation
import Tengoku.Seed.Analysis.LocallyConvex.Polar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 连续零化子与子空间闭包

子空间 `S` 的连续零化子由所有在 `S` 上恒为零的连续线性泛函组成。Mathlib 的
`StrongDual.polarSubmodule ℝ S` 正好承载这一对象。本文件进一步用凸分离证明：被全部连续零化子
消灭的向量，恰好组成 `S` 的拓扑闭包。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 属于连续零化子，等价于在原子空间每个向量上取零。

> **Entry**: functional-analysis.subspace.annihilator-closure-/
theorem mem_continuousAnnihilator_iff (S : Submodule ℝ E) (f : StrongDual ℝ E) :
    f ∈ StrongDual.polarSubmodule ℝ S ↔ ∀ x ∈ S, f x = 0 := by
  exact StrongDual.mem_polarSubmodule ℝ S f

/-- 连续零化子反转子空间包含关系。-/
theorem continuousAnnihilator_anti {S T : Submodule ℝ E} (hST : S ≤ T) :
    StrongDual.polarSubmodule ℝ T ≤ StrongDual.polarSubmodule ℝ S := by
  intro f hf
  rw [mem_continuousAnnihilator_iff] at hf ⊢
  exact fun x hx ↦ hf x (hST hx)

/-- 双零化子闭包刻画：一个向量属于 `S` 的闭包，当且仅当所有消灭 `S` 的连续泛函也消灭它。-/
theorem mem_topologicalClosure_iff_forall_annihilator (S : Submodule ℝ E) (x : E) :
    x ∈ S.topologicalClosure ↔
      ∀ f : StrongDual ℝ E, f ∈ StrongDual.polarSubmodule ℝ S → f x = 0 := by
  constructor
  · intro hx f hf
    apply S.topologicalClosure_minimal _ f.isClosed_ker hx
    intro y hy
    exact (mem_continuousAnnihilator_iff S f).mp hf y hy
  · intro hx
    by_contra hxc
    obtain ⟨f, c, hfS, hcfx⟩ :=
      separate_closed_convex_point (s := (S.topologicalClosure : Set E))
        S.topologicalClosure.convex S.isClosed_topologicalClosure hxc
    have hcpos : 0 < c := by
      simpa using hfS 0 S.topologicalClosure.zero_mem
    have hfzero : ∀ y ∈ S, f y = 0 := by
      intro y hy
      by_contra hfy
      have hzmem : ((c + 1) / f y) • y ∈ S.topologicalClosure :=
        S.le_topologicalClosure (S.smul_mem ((c + 1) / f y) hy)
      have hz := hfS _ hzmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfy] at hz
      linarith
    have hfxzero := hx f ((mem_continuousAnnihilator_iff S f).mpr hfzero)
    rw [hfxzero] at hcfx
    linarith

/-- 对闭子空间，连续泛函的共同零点精确恢复该子空间。-/
theorem mem_closedSubspace_iff_forall_annihilator (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) :
    x ∈ S ↔ ∀ f : StrongDual ℝ E, f ∈ StrongDual.polarSubmodule ℝ S → f x = 0 := by
  constructor
  · intro hx
    exact (mem_topologicalClosure_iff_forall_annihilator S x).mp (S.le_topologicalClosure hx)
  · intro hx
    exact S.topologicalClosure_minimal le_rfl hS
      ((mem_topologicalClosure_iff_forall_annihilator S x).mpr hx)

end SandronesLibrary.FunctionalAnalysis
