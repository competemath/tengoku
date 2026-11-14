/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathHomotopyStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 一般同伦与相对同伦

本模块解释 Mathlib 的一般 `ContinuousMap.Homotopy` 与相对 `ContinuousMap.HomotopyRel`
承载及其复合行为，不复用已经冻结的 `TextbookTopology.Homotopy` 实现。

当前条目：

* `topology.homotopy.standard`.
-/

open Set

namespace SandronesLibrary.Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- 一般同伦恰好是时间零与时间一切片为指定连续映射的连续变形；第一坐标是同伦时间。

> **Entry**: topology.homotopy.standard-/
theorem nonempty_homotopy_iff_exists_continuous_deformation
    {f g : C(X, Y)} :
    Nonempty (f.Homotopy g) ↔
      ∃ F : unitInterval × X → Y, Continuous F ∧
        (∀ x, F (0, x) = f x) ∧
        (∀ x, F (1, x) = g x) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H, H.continuous, H.apply_zero, H.apply_one⟩
  · rintro ⟨F, hF, hzero, hone⟩
    exact ⟨{
      toFun := F
      continuous_toFun := hF
      map_zero_left := hzero
      map_one_left := hone
    }⟩

/-- 相对 `S` 的同伦要求 `S` 中的点在全部时间保持固定，而不只是两个端点映射在 `S` 上相等。-/
theorem nonempty_homotopyRel_iff_exists_continuous_deformation_fixed_on
    {f g : C(X, Y)} {S : Set X} :
    Nonempty (f.HomotopyRel g S) ↔
      ∃ F : unitInterval × X → Y, Continuous F ∧
        (∀ x, F (0, x) = f x) ∧
        (∀ x, F (1, x) = g x) ∧
        (∀ t x, x ∈ S → F (t, x) = f x) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H, H.continuous, H.apply_zero, H.apply_one, fun t x hx ↦ H.eq_fst t hx⟩
  · rintro ⟨F, hF, hzero, hone, hfixed⟩
    exact ⟨{
      toHomotopy := {
        toFun := F
        continuous_toFun := hF
        map_zero_left := hzero
        map_one_left := hone
      }
      prop' := hfixed
    }⟩

/-- 两个相容同伦的复合使用同一时间坐标，并逐点复合它们的空间取值。-/
theorem homotopy_comp_apply
    {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)}
    (G : g₀.Homotopy g₁) (F : f₀.Homotopy f₁)
    (z : unitInterval × X) :
    G.comp F z = G (z.1, F z) := by
  rfl

/-- 对相对 `S` 同伦的每一阶段后复合连续映射，仍得到相对同一个集合 `S` 的同伦。-/
theorem homotopyRel_compContinuousMap_apply
    {f₀ f₁ : C(X, Y)} {S : Set X}
    (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z))
    (z : unitInterval × X) :
    F.compContinuousMap g z = g (F z) := by
  rfl

end SandronesLibrary.Topology
