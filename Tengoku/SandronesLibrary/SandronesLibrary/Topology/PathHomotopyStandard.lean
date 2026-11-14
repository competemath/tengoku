/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Path
import Tengoku.Seed.Topology.Homotopy.Path
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 道路之间的标准同伦

本模块把 Mathlib 的 `Path.Homotopy` 直接解释为端点保持固定的二参数连续变形，不让新的拓扑
课程接口绕回已经冻结的 `TextbookTopology` 同伦结构。

当前条目：

* `topology.homotopy.path-homotopy-standard`.
-/

open Set

namespace SandronesLibrary.Topology

universe u

variable {X : Type u} [TopologicalSpace X]
variable {x y : X} {p q r : _root_.Path x y}

/-- 标准道路同伦恰好是正方形上的连续映射：时间零与时间一切片分别为两条道路，并且两个道路
端点在全部时间内保持固定。第一坐标是同伦时间，第二坐标是道路位置。

> **Entry**: topology.homotopy.path-homotopy-standard
@isnad1 id=iff.0h5v.s8.59d796def29c from=translated src=- shape=8ae9fd69 vocab=61dd5b8d
-/
theorem nonempty_pathHomotopy_iff_exists_fixed_endpoint_deformation :
    Nonempty (p.Homotopy q) ↔
      ∃ F : unitInterval × unitInterval → X, Continuous F ∧
        (∀ s, F (0, s) = p s) ∧
        (∀ s, F (1, s) = q s) ∧
        (∀ t, F (t, 0) = x) ∧
        (∀ t, F (t, 1) = y) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H, H.continuous, H.apply_zero, H.apply_one, H.source, H.target⟩
  · rintro ⟨F, hF, hzero, hone, hsource, htarget⟩
    refine ⟨{
      toHomotopy := {
        toFun := F
        continuous_toFun := hF
        map_zero_left := hzero
        map_one_left := hone
      }
      prop' := ?_
    }⟩
    intro t s hs
    rcases hs with rfl | rfl
    · exact (hsource t).trans p.source.symm
    · exact (htarget t).trans p.target.symm

/-- 反身道路同伦在同伦时间方向保持常值。
@isnad1 id=eq.0h5v.s8.9d0077b3baa6 from=translated src=- shape=b5e48838 vocab=37a2408a
-/
theorem pathHomotopy_refl_apply (p : _root_.Path x y)
    (z : unitInterval × unitInterval) :
    _root_.Path.Homotopy.refl p z = p z.2 := by
  exact _root_.Path.Homotopy.refl_apply p z

/-- 道路同伦的对称操作只反射时间坐标，并不反转其中的道路。
@isnad1 id=eq.0h7v.s9.b1dbf9f054f6 from=translated src=- shape=816a67be vocab=4ed105a6
-/
theorem pathHomotopy_symm_apply (H : p.Homotopy q)
    (z : unitInterval × unitInterval) :
    H.symm z = H (unitInterval.symm z.1, z.2) := by
  exact _root_.Path.Homotopy.symm_apply H z

/-- 复合同伦的前半段把时间加倍后送入第一个变形。
@isnad1 id=eq.1h9v.s9.7d75bffb4421 from=translated src=- shape=d5865b63 vocab=16e89fba
-/
theorem pathHomotopy_trans_apply_of_le (H : p.Homotopy q) (K : q.Homotopy r)
    (z : unitInterval × unitInterval) (h : (z.1 : ℝ) ≤ 1 / 2) :
    H.trans K z = H (⟨2 * z.1, by constructor <;> linarith [z.1.2.1, z.1.2.2]⟩, z.2) := by
  rw [_root_.Path.Homotopy.trans_apply]
  simp only [dite_eq_left h]

/-- 复合同伦的后半段用平移后的二倍时间走过第二个变形。
@isnad1 id=eq.1h9v.s9.1c9fd5661cbc from=translated src=- shape=7bec05bf vocab=555ea172
-/
theorem pathHomotopy_trans_apply_of_not_le (H : p.Homotopy q) (K : q.Homotopy r)
    (z : unitInterval × unitInterval) (h : ¬(z.1 : ℝ) ≤ 1 / 2) :
    H.trans K z = K (⟨2 * z.1 - 1, by constructor <;> linarith [z.1.2.1, z.1.2.2]⟩, z.2) := by
  rw [_root_.Path.Homotopy.trans_apply]
  simp only [dite_eq_right h]

end SandronesLibrary.Topology
