/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Basic
public import Tengoku.Seed.MeasureTheory.Measure.OpenPos
public import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Disks and the full-dimensional boundary case
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch

variable {n k : ℕ}

/-- The radius-one disk with center a and direction V, as an ambient set.-/
def unitDisk (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) : Set
    (EuclideanSpace ℝ (Fin n)) :=
  {x | x - a ∈ V ∧ ‖x - a‖ ≤ 1}

/--
@isnad1 id=eq.0h3v.s11.c220928dd254 from=translated src=- shape=86e9f59d vocab=96bff7fb
-/
theorem unitDisk_eq_image (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    unitDisk V a = (fun v : V ↦ a + v) '' Metric.closedBall (0 : V) 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨x - a, hx.1⟩, ?_, by simp⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hx.2
  · rintro ⟨v, hv, rfl⟩
    simpa [unitDisk, Metric.mem_closedBall, dist_zero_right] using And.intro v.property hv

/--
@isnad1 id=iscompac.0h3v.s7.a688df2c12d9 from=translated src=- shape=2e99d3e8 vocab=ef6becf8
-/
theorem isCompact_unitDisk (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    IsCompact (unitDisk V a) := by
  rw [unitDisk_eq_image]
  exact (isCompact_closedBall (0 : V) 1).image (continuous_const.add continuous_subtype_val)

/--
@isnad1 id=iff.0h3v.s9.379e7d310606 from=translated src=- shape=6313d67c vocab=65139721
-/
theorem isBesicovitch_iff_unitDisk_subset {E : Set (EuclideanSpace ℝ (Fin n))} :
    IsBesicovitch k E ↔ ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ V = k →
      ∃ a, unitDisk V a ⊆ E := by
  constructor
  · intro h V hV
    obtain ⟨a, ha⟩ := h V hV
    refine ⟨a, fun x hx ↦ ?_⟩
    simpa using ha (x - a) hx.1 hx.2
  · intro h V hV
    obtain ⟨a, ha⟩ := h V hV
    exact ⟨a, fun v hv hn ↦ ha (by simpa [unitDisk] using And.intro hv hn)⟩

/-- The full-dimensional disk property implies positive volume, even without measurability.
@isnad1 id=lt.1h2v.s8.2c29256362b4 from=translated src=- shape=ca16ed71 vocab=ce8572cf
-/
theorem volume_pos_of_isBesicovitch_self {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : IsBesicovitch n E) :
    0 < volume E := by
  obtain ⟨a, ha⟩ := hE ⊤ (by simp)
  refine (Metric.measure_ball_pos volume a (by norm_num : (0 : ℝ) < 1)).trans_le
    (measure_mono fun x hx ↦ ?_)
  have hn : ‖x - a‖ ≤ 1 := (by simpa [dist_eq_norm] using hx : ‖x - a‖ < 1).le
  simpa using ha (x - a) (Submodule.mem_top) hn

end NKBesicovitch
