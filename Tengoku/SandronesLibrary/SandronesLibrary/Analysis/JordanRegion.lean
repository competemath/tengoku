/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.MultivariableIntegration
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Closure
import Tengoku.Seed.MeasureTheory.Order.UpperLower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jordan 可测区域

本模块采用教材等价刻画：有界集合的边界具有零体积。由此推出区域的零可测性、
有限体积、内部与闭包的体积一致性，以及积分不受加入边界影响。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory
open scoped ENNReal

abbrev JordanEuc (n : ℕ) := Fin n → ℝ

/-- 教材中的 Jordan 可测有界区域：区域有界且边界的 `n` 维体积为零。

> **Entry**: analysis.multivariable.jordan-region-/
def IsJordanMeasurable {n : ℕ} (s : Set (JordanEuc n)) : Prop :=
  Bornology.IsBounded s ∧ volume (frontier s) = 0

/-- Jordan 可测区域对 Lebesgue 测度是零可测的。-/
theorem IsJordanMeasurable.nullMeasurableSet {n : ℕ} {s : Set (JordanEuc n)}
    (hs : IsJordanMeasurable s) : NullMeasurableSet s volume := by
  exact nullMeasurableSet_of_null_frontier hs.2

/-- Jordan 可测区域体积有限。-/
theorem IsJordanMeasurable.volume_lt_top {n : ℕ} {s : Set (JordanEuc n)}
    (hs : IsJordanMeasurable s) : volume s < ∞ := by
  exact hs.1.measure_lt_top

/-- Jordan 可测区域与其内部具有相同体积。-/
theorem IsJordanMeasurable.volume_interior {n : ℕ} {s : Set (JordanEuc n)}
    (hs : IsJordanMeasurable s) : volume (interior s) = volume s := by
  exact measure_interior_of_null_frontier hs.2

/-- Jordan 可测区域与其闭包具有相同体积。-/
theorem IsJordanMeasurable.volume_closure {n : ℕ} {s : Set (JordanEuc n)}
    (hs : IsJordanMeasurable s) : volume (closure s) = volume s := by
  exact measure_closure_of_null_frontier hs.2

/-- Jordan 可测区域的闭包仍然 Jordan 可测。-/
theorem IsJordanMeasurable.closure_isJordanMeasurable {n : ℕ} {s : Set (JordanEuc n)}
    (hs : IsJordanMeasurable s) : IsJordanMeasurable (closure s) := by
  exact ⟨hs.1.closure, measure_mono_null frontier_closure_subset hs.2⟩

/-- 在 Jordan 可测区域上积分时，加入边界不改变积分值。-/
theorem IsJordanMeasurable.setIntegral_closure {n : ℕ} {s : Set (JordanEuc n)}
    (hs : IsJordanMeasurable s) (f : JordanEuc n → ℝ) :
    ∫ x in _root_.closure s, f x = ∫ x in s, f x := by
  exact setIntegral_congr_set (closure_ae_eq_of_null_frontier hs.2)

end SandronesLibrary.Analysis.Multivariable
