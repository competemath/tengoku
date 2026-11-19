/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive finite volume of thickened unit disks

Every positive thickness gives a plate of positive finite volume, including
zero-dimensional directions and the full-dimensional boundary.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

/--
@isnad1 id=lt.1h4v.s8.c090a080d83a from=translated src=- shape=3b28f791 vocab=7e0be2dc
-/
theorem volume_plate_pos {δ : ℝ} (hδ : 0 < δ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    0 < volume (plate δ V a) := by
  refine (Metric.measure_ball_pos volume a hδ).trans_le (measure_mono ?_)
  exact Metric.ball_subset_thickening (by simp [unitDisk] : a ∈ unitDisk V a) δ

/--
@isnad1 id=lt.0h4v.s8.fb3f71edcd6f from=translated src=- shape=264ad949 vocab=3da79dd9
-/
theorem volume_plate_lt_top (δ : ℝ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    volume (plate δ V a) < ⊤ :=
  (isCompact_unitDisk V a).isBounded.thickening.measure_lt_top

/--
@isnad1 id=le.0h4v.s7.206e1eb49f20 from=translated src=- shape=7161b1c0 vocab=2a5c2bac
-/
theorem plate_subset_ball (δ : ℝ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : plate δ V a ⊆ Metric.ball a (δ + 1) := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.mp hx
  have hza : dist z a ≤ 1 := by simpa only [dist_eq_norm] using hz.2
  exact (dist_triangle x z a).trans_lt (add_lt_add_of_lt_of_le hxz hza)

end NKBesicovitch
