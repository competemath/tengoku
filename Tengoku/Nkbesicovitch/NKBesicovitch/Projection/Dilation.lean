/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Estimates
public import Tengoku.Seed.MeasureTheory.Group.MeasurableEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spatial dilation of line families

Dilating both intercepts and slopes by `r > 0` multiplies line volume by
`r^(2m)` and each projection volume by `r^m`. Parallel-fiber volumes also
scale by `r^m`; dilation of the slope parameter preserves null sets, so
the essential supremum has exactly the same scaling factor.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal Pointwise

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=eq.0h4v.s7.604d5e32c772 from=translated src=- shape=1183eb4a vocab=ae8da648
-/
theorem atHeight_smul (t r : ℝ) (g : Line m) : atHeight t (r • g) = r • atHeight t g := by
  simp only [atHeight, Prod.smul_fst, Prod.smul_snd, smul_add, smul_comm t r]

/--
@isnad1 id=eq.0h4v.s7.a06a0af64377 from=translated src=- shape=7992d4b5 vocab=a4835df9
-/
theorem atHeight_image_smul (t r : ℝ) (G : Set (Line m)) :
    atHeight t '' (r • G) = r • (atHeight t '' G) := by
  ext y
  constructor
  · rintro ⟨g, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨atHeight t h, ⟨h, hh, rfl⟩, (atHeight_smul t r h).symm⟩
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨r • g, ⟨g, hg, rfl⟩, atHeight_smul t r g⟩

/--
@isnad1 id=eq.1h4v.s9.5a848c5f3faa from=translated src=- shape=30bf44c3 vocab=fbdb1169
-/
theorem volume_projection_smul (t : ℝ) {r : ℝ} (hr : 0 ≤ r) (G : Set (Line m)) :
    volume (atHeight t '' (r • G)) = ENNReal.ofReal (r ^ m) * volume (atHeight t '' G) := by
  rw [atHeight_image_smul]
  simpa only [finrank_euclideanSpace_fin] using
    Measure.addHaar_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin m))) hr
      (atHeight t '' G)

/--
@isnad1 id=eq.1h3v.s10.21d901e23bbe from=translated src=- shape=a719500b vocab=3291659e
-/
theorem volume_lineFamily_smul {r : ℝ} (hr : 0 ≤ r) (G : Set (Line m)) :
    volume (r • G) = ENNReal.ofReal ((r ^ m) ^ 2) * volume G := by
  have : Measure.IsAddHaarMeasure (volume : Measure (Line m)) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin m))))
    infer_instance
  simpa only [Module.finrank_prod, finrank_euclideanSpace_fin, pow_add, pow_two] using
    Measure.addHaar_smul_of_nonneg (volume : Measure (Line m)) hr G

/--
@isnad1 id=eq.1h4v.s9.9cde80a73ab1 from=translated src=- shape=1eebb3a1 vocab=3a9e7c12
-/
theorem volume_parallelFiber_smul {r : ℝ} (hr : 0 < r) (G : Set (Line m))
    (ξ : EuclideanSpace ℝ (Fin m)) :
    volume {x | (x, ξ) ∈ r • G} = ENNReal.ofReal (r ^ m) * volume {x | (x, r⁻¹ • ξ) ∈ G} := by
  have hs : {x | (x, ξ) ∈ r • G} = r • {x | (x, r⁻¹ • ξ) ∈ G} := by
    ext x
    simp only [mem_ofPred_eq, mem_smul_set_iff_inv_smul_mem₀ hr.ne', Prod.smul_mk]
  rw [hs]
  simpa only [finrank_euclideanSpace_fin] using
    Measure.addHaar_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin m))) hr.le
      {x | (x, r⁻¹ • ξ) ∈ G}

/--
@isnad1 id=eq.1h3v.s7.305f4befe4f5 from=translated src=- shape=86b5c061 vocab=3ffea964
-/
theorem parallelMultiplicity_smul {r : ℝ} (hr : 0 < r) (G : Set (Line m)) :
    parallelMultiplicity (r • G) = ENNReal.ofReal (r ^ m) * parallelMultiplicity G := by
  unfold parallelMultiplicity
  simp_rw [volume_parallelFiber_smul hr]
  rw [ENNReal.essSup_const_mul]
  congr 1
  let f (ξ : EuclideanSpace ℝ (Fin m)) := volume {x | (x, ξ) ∈ G}
  have h := (measurableEmbedding_const_smul₀ (α := EuclideanSpace ℝ (Fin m))
    (inv_ne_zero hr.ne')).essSup_map_measure (g := f) (μ := volume)
  have hscalar : ENNReal.ofReal |((r⁻¹) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr
      (inv_ne_zero (pow_ne_zero _ (inv_ne_zero hr.ne'))))).ne'
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'),
    essSup_ennreal_smul_measure hscalar] at h
  exact h.symm

end NKBesicovitch.Projection
