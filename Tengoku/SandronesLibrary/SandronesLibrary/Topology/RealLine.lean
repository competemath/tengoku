/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Constructions
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Topology.Instances.Real.Lemmas
import Tengoku.Seed.Topology.UnitInterval
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 实直线与单位区间的拓扑

正式课程接口直接使用 Mathlib 的标准实数拓扑和 `unitInterval`，并用正半径
ε 邻域刻画解释教材语义。文件后半保留旧显式构造，仅供已提交下游迁移使用。

Current entry:

* `topology.foundation.real-line`.
-/

open Set

namespace SandronesLibrary.Topology

/-- 标准实数拓扑中的开集，恰好满足教材的正半径绝对值邻域刻画。

> **Entry**: topology.foundation.real-line-/
theorem real_isOpen_iff_abs (s : Set ℝ) :
    _root_.IsOpen s ↔
      ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ y, |y - x| < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨ε, hε, hball⟩ := h x hx
    exact ⟨ε, hε, fun y hy ↦ hball (by simpa [Real.dist_eq] using hy)⟩
  · intro h x hx
    obtain ⟨ε, hε, hball⟩ := h x hx
    exact ⟨ε, hε, fun y hy ↦ hball y (by simpa [Real.dist_eq] using hy)⟩

/-- Mathlib 的道路参数类型 `unitInterval` 就是闭区间 `Set.Icc 0 1`。-/
theorem unitInterval_eq_Icc : unitInterval = Set.Icc (0 : ℝ) 1 :=
  rfl

end SandronesLibrary.Topology

namespace SandronesLibrary.Topology.TextbookTopology

/-- A subset of the real line is open when each of its points contains a positive epsilon-ball
inside the subset.

> **Entry**: topology.foundation.real-line-/
def realLine : TextbookTopology ℝ where
  IsOpen s := ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ y, |y - x| < ε → y ∈ s
  isOpen_univ := by
    intro x hx
    exact ⟨1, zero_lt_one, by simp⟩
  isOpen_inter s t hs ht := by
    intro x hx
    obtain ⟨εs, hεs, hsball⟩ := hs x hx.1
    obtain ⟨εt, hεt, htball⟩ := ht x hx.2
    refine ⟨min εs εt, lt_min hεs hεt, fun y hy ↦ ?_⟩
    exact ⟨hsball y (lt_of_lt_of_le hy (min_le_left _ _)),
      htball y (lt_of_lt_of_le hy (min_le_right _ _))⟩
  isOpen_sUnion S hS := by
    intro x hx
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨ε, hε, hball⟩ := hS s hsS x hxs
    exact ⟨ε, hε, fun y hy ↦ ⟨s, hsS, hball y hy⟩⟩

/-- The closed unit interval as a type.-/
def UnitInterval := {t : ℝ // 0 ≤ t ∧ t ≤ 1}

namespace UnitInterval

/-- The left endpoint of the unit interval.-/
def zero : UnitInterval := ⟨0, le_rfl, zero_le_one⟩

/-- The right endpoint of the unit interval.-/
def one : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

@[simp] theorem zero_val : zero.1 = 0 := rfl

@[simp] theorem one_val : one.1 = 1 := rfl

end UnitInterval

/-- The unit interval carries the subspace topology inherited from the textbook real line.-/
def unitInterval : TextbookTopology UnitInterval :=
  subspace {t : ℝ | 0 ≤ t ∧ t ≤ 1} realLine

/-- A subset of the unit interval is open exactly when each of its points contains a relative
epsilon-neighborhood inside the subset.-/
theorem isOpen_unitInterval_iff (s : Set UnitInterval) :
    unitInterval.IsOpen s ↔
      ∀ t ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ u : UnitInterval, |u.1 - t.1| < ε → u ∈ s := by
  constructor
  · rintro ⟨v, hv, rfl⟩ t ht
    obtain ⟨ε, hε, hball⟩ := hv t.1 ht
    exact ⟨ε, hε, fun u hu ↦ hball u.1 hu⟩
  · intro hs
    let v : Set ℝ := {x | ∃ t ∈ s, ∃ ε : ℝ, 0 < ε ∧
      (∀ u : UnitInterval, |u.1 - t.1| < ε → u ∈ s) ∧ |x - t.1| < ε}
    have hv : realLine.IsOpen v := by
      intro x hx
      obtain ⟨t, ht, ε, hε, hinside, hxt⟩ := hx
      refine ⟨ε - |x - t.1|, sub_pos.mpr hxt, fun y hy ↦ ?_⟩
      refine ⟨t, ht, ε, hε, hinside, ?_⟩
      calc
        |y - t.1| = |(y - x) + (x - t.1)| := by rw [sub_add_sub_cancel]
        _ ≤ |y - x| + |x - t.1| := abs_add_le _ _
        _ < (ε - |x - t.1|) + |x - t.1| := add_lt_add_left hy _
        _ = ε := sub_add_cancel ε |x - t.1|
    refine ⟨v, hv, ?_⟩
    ext t
    constructor
    · rintro ⟨q, hq, ε, hε, hinside, htq⟩
      exact hinside t htq
    · intro ht
      obtain ⟨ε, hε, hinside⟩ := hs t ht
      exact ⟨t, ht, ε, hε, hinside, by simpa using hε⟩

/-- Continuity from the unit interval can be checked by relative epsilon-neighborhoods of each
point and each open set containing its image.-/
theorem continuous_from_unitInterval_iff {X : Type*} (τX : TextbookTopology X)
    (f : UnitInterval → X) :
    Continuous unitInterval τX f ↔
      ∀ t v, τX.IsOpen v → f t ∈ v →
        ∃ ε : ℝ, 0 < ε ∧ ∀ u : UnitInterval, |u.1 - t.1| < ε → f u ∈ v := by
  constructor
  · intro hf t v hv hft
    exact (isOpen_unitInterval_iff (f ⁻¹' v)).mp (hf v hv) t hft
  · intro hf v hv
    apply (isOpen_unitInterval_iff (f ⁻¹' v)).mpr
    intro t hft
    exact hf t v hv hft

/-- The inclusion of the unit interval into the real line is continuous by construction.-/
theorem continuous_unitInterval_val :
    Continuous unitInterval realLine (Subtype.val : UnitInterval → ℝ) :=
  continuous_subtype_val _ realLine

/-- Reflection about `1 / 2` on the real line.-/
def realReflection (x : ℝ) : ℝ := 1 - x

/-- Reflection about `1 / 2` is continuous for the textbook real-line topology.-/
theorem continuous_realReflection : Continuous realLine realLine realReflection := by
  intro s hs x hx
  obtain ⟨ε, hε, hball⟩ := hs (realReflection x) hx
  refine ⟨ε, hε, fun y hy ↦ hball (realReflection y) ?_⟩
  simpa [realReflection, abs_sub_comm] using hy

/-- Reflection of the closed unit interval, sending `t` to `1 - t`.-/
def UnitInterval.reflect (t : UnitInterval) : UnitInterval :=
  ⟨1 - t.1, sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩

@[simp] theorem UnitInterval.reflect_val (t : UnitInterval) : t.reflect.1 = 1 - t.1 := rfl

@[simp] theorem UnitInterval.reflect_zero : UnitInterval.zero.reflect = UnitInterval.one := by
  apply Subtype.ext
  simp [UnitInterval.reflect, UnitInterval.zero, UnitInterval.one]

@[simp] theorem UnitInterval.reflect_one : UnitInterval.one.reflect = UnitInterval.zero := by
  apply Subtype.ext
  simp [UnitInterval.reflect, UnitInterval.zero, UnitInterval.one]

@[simp] theorem UnitInterval.reflect_reflect (t : UnitInterval) : t.reflect.reflect = t := by
  apply Subtype.ext
  simp

/-- Unit-interval reflection is continuous in the Sandrone subspace topology.-/
theorem continuous_unitInterval_reflect :
    Continuous unitInterval unitInterval UnitInterval.reflect := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := hu
  have hopen : realLine.IsOpen (realReflection ⁻¹' v) := continuous_realReflection v hv
  refine ⟨realReflection ⁻¹' v, hopen, ?_⟩
  ext t
  rfl

end SandronesLibrary.Topology.TextbookTopology
