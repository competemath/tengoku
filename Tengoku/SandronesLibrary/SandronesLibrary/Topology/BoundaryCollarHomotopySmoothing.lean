/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopyStandard
import Tengoku.Seed.Geometry.Manifold.SmoothApprox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 边界 collar 条件下的道路同伦相对平滑化

本文件证明一个严格受限的桥：若标准道路同伦有全局连续延拓，并且该延拓在闭单位方形四边的某个
邻域中已经二阶光滑，则可在保持四边不变、保持像仍落在指定开集的同时，把同伦替换为二阶光滑
同伦。它不处理边界道路仅连续或分段 `C¹` 的一般情形。

当前条目：

* `topology.homotopy.boundary-collar-smoothing`。
-/

open Set
open scoped unitInterval

namespace SandronesLibrary.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 实平面中的闭单位方形。

> **Entry**: topology.homotopy.boundary-collar-smoothing-/
def closedUnitSquare : Set (ℝ × ℝ) := Icc (0, 0) (1, 1)

/-- 闭单位方形的四条边，显式写成四个积集合的并。-/
def closedUnitSquareBoundary : Set (ℝ × ℝ) :=
  ({0} ×ˢ Icc 0 1) ∪ ({1} ×ˢ Icc 0 1) ∪
    (Icc 0 1 ×ˢ {0}) ∪ (Icc 0 1 ×ˢ {1})

/-- 闭单位方形的四边是闭集，因此可以作为相对平滑逼近中必须逐点保持的集合。-/
theorem isClosed_closedUnitSquareBoundary : IsClosed closedUnitSquareBoundary := by
  exact (((isClosed_singleton.prod isClosed_Icc).union
    (isClosed_singleton.prod isClosed_Icc)).union
    (isClosed_Icc.prod isClosed_singleton)).union
    (isClosed_Icc.prod isClosed_singleton)

/-- 若连续函数在闭集 `S` 的某个邻域已经 `C²`，且闭方形像位于开集 `U`，则存在全局 `C²`
逼近：它在 `S` 上与原函数严格相等，并且闭方形像仍位于 `U`。-/
theorem exists_contDiffTwo_approx_eqOn_mapsTo_open
    (f : ℝ × ℝ → E) (hf : Continuous f) {S V : Set (ℝ × ℝ)} {U : Set E}
    (hS : IsClosed S) (hV : V ∈ nhdsSet S) (hfV : ContDiffOn ℝ 2 f V)
    (hU : IsOpen U) (hfU : MapsTo f closedUnitSquare U) :
    ∃ g : ℝ × ℝ → E,
      ContDiff ℝ 2 g ∧ EqOn g f S ∧ MapsTo g closedUnitSquare U := by
  have hQ : IsCompact closedUnitSquare := isCompact_Icc
  have hK : IsCompact (f '' closedUnitSquare) := hQ.image hf
  obtain ⟨δ, hδpos, hδ⟩ :=
    hK.exists_cthickening_subset_open hU (image_subset_iff.mpr hfU)
  obtain ⟨g, hgC2, hgclose, hgS, _⟩ :=
    hf.exists_contDiff_approx_and_eqOn 2 continuous_const (fun _ ↦ hδpos) hS hV hfV
  refine ⟨g, hgC2, hgS, ?_⟩
  intro z hz
  apply hδ
  exact Metric.mem_cthickening_of_dist_le (g z) (f z) δ (f '' closedUnitSquare)
    ⟨z, hz, rfl⟩ (le_of_lt (hgclose z))

/-- 一个连续替换若在方形四边与原道路同伦延拓相等，则限制回单位方形后仍是同一对道路之间、
相对两个端点的标准 `Path.Homotopy`。-/
def pathHomotopyOfEqOnSquareBoundary
    {x y : E} {p q : Path x y} (F : p.Homotopy q)
    (f g : ℝ × ℝ → E) (hg : Continuous g)
    (hfF : ∀ z : unitInterval × unitInterval, f (z.1, z.2) = F z)
    (hgf : EqOn g f closedUnitSquareBoundary) : p.Homotopy q where
  toHomotopy := {
    toFun z := g (z.1, z.2)
    continuous_toFun := hg.comp (by fun_prop)
    map_zero_left := fun s ↦ by
      rw [hgf (by simp [closedUnitSquareBoundary])]
      rw [hfF]
      simp
    map_one_left := fun s ↦ by
      rw [hgf (by simp [closedUnitSquareBoundary])]
      rw [hfF]
      simp
  }
  prop' := fun t s hs ↦ by
    rcases hs with rfl | rfl
    · change g (t, 0) = p 0
      rw [hgf (by simp [closedUnitSquareBoundary])]
      calc
        f (t, 0) = F (t, 0) := by simpa using hfF (t, 0)
        _ = p 0 := by simp
    · change g (t, 1) = p 1
      rw [hgf (by simp [closedUnitSquareBoundary])]
      calc
        f (t, 1) = F (t, 1) := by simpa using hfF (t, 1)
        _ = p 1 := by simp

/-- 上述限制所得同伦的标准双重钳位延拓，在闭单位方形上继承全局函数 `g` 的 `C²` 正则性。-/
theorem pathHomotopyOfEqOnSquareBoundary_standardExtension_contDiffOn
    {x y : E} {p q : Path x y} (F : p.Homotopy q)
    (f g : ℝ × ℝ → E) (hg : ContDiff ℝ 2 g)
    (hfF : ∀ z : unitInterval × unitInterval, f (z.1, z.2) = F z)
    (hgf : EqOn g f closedUnitSquareBoundary) :
    let H := pathHomotopyOfEqOnSquareBoundary F f g hg.continuous hfF hgf
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H.toHomotopy.extend xy.1) xy.2)
      (Icc 0 1) := by
  let H := pathHomotopyOfEqOnSquareBoundary F f g hg.continuous hfF hgf
  apply hg.contDiffOn.congr
  intro xy hxy
  have hx1 : xy.1 ∈ Icc (0 : ℝ) 1 := ⟨hxy.1.1, hxy.2.1⟩
  have hx2 : xy.2 ∈ Icc (0 : ℝ) 1 := ⟨hxy.1.2, hxy.2.2⟩
  rw [Set.IccExtend_of_mem zero_le_one _ hx2]
  rw [H.toHomotopy.extend_apply_of_mem_I hx1]
  rfl

/-- 边界 collar 相对平滑化：若道路同伦的一个全局连续延拓在方形四边某邻域已 `C²`，且原同伦
像位于开集 `U`，则存在保持四边和开域像的标准道路同伦，其双重 `IccExtend` 在闭方形上 `C²`。

该结论不适用于任意连续或仅分段 `C¹` 的边界道路。-/
theorem exists_contDiffTwo_pathHomotopy_of_boundaryCollar
    {x y : E} {p q : Path x y} (F : p.Homotopy q)
    (f : ℝ × ℝ → E) (hf : Continuous f)
    (hfF : ∀ z : unitInterval × unitInterval, f (z.1, z.2) = F z)
    {V : Set (ℝ × ℝ)} (hV : V ∈ nhdsSet closedUnitSquareBoundary)
    (hfV : ContDiffOn ℝ 2 f V) {U : Set E} (hU : IsOpen U)
    (hFU : ∀ s t : unitInterval, F (s, t) ∈ U) :
    ∃ H : p.Homotopy q,
      (∀ s t : unitInterval, H (s, t) ∈ U) ∧
      ContDiffOn ℝ 2
        (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H.toHomotopy.extend xy.1) xy.2)
        (Icc 0 1) := by
  have hfU : MapsTo f closedUnitSquare U := by
    intro z hz
    let s : unitInterval := ⟨z.1, hz.1.1, hz.2.1⟩
    let t : unitInterval := ⟨z.2, hz.1.2, hz.2.2⟩
    rw [hfF (s, t)]
    exact hFU s t
  obtain ⟨g, hgC2, hgf, hgU⟩ := exists_contDiffTwo_approx_eqOn_mapsTo_open
    f hf isClosed_closedUnitSquareBoundary hV hfV hU hfU
  let H := pathHomotopyOfEqOnSquareBoundary F f g hgC2.continuous hfF hgf
  refine ⟨H, ?_, ?_⟩
  · intro s t
    exact hgU (x := (s.1, t.1)) ⟨⟨s.2.1, t.2.1⟩, ⟨s.2.2, t.2.2⟩⟩
  · exact pathHomotopyOfEqOnSquareBoundary_standardExtension_contDiffOn
      F f g hgC2 hfF hgf

end SandronesLibrary.Topology
