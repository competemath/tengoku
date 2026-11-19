/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.NormalIsometry
public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.SphereMeasure
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.Spherical
public import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of geometric X-ray direction norms

In an orthogonal frame the displacement domain is fixed, so Tonelli
gives joint measurability. The norm is unchanged by transporting the
frame. A surjective Borel orbit map from the compact orthogonal group
then transfers measurability to the unit sphere.
The resulting norm identity includes the normalization factor for sphere measure.
-/

public section

open MeasureTheory Submodule Metric
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {n : ℕ}

/--
@isnad1 id=eq.1h5v.s15.a848195b4439 from=translated src=- shape=ad316f48 vocab=83b005fd
-/
theorem directionXRayNorm_rotate {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) (r : ℝ≥0∞) (u : Rotations n)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    directionXRayNorm f r (Rotations.rotateSphere u v) =
      directionXRayNorm (f ∘ Unitary.linearIsometryEquiv u) r v := by
  let e := Unitary.linearIsometryEquiv u
  have hm : Measurable (fun y : (ℝ ∙ e v)ᗮ ↦
      ∫⁻ t : ℝ, f ((y : EuclideanSpace ℝ (Fin n)) + t • e v)) := by
    have h : Measurable (fun z : (ℝ ∙ e v)ᗮ × ℝ ↦
        f ((z.1 : EuclideanSpace ℝ (Fin n)) + z.2 • e v)) := hf.comp (by fun_prop)
    exact h.lintegral_prod_right' (ν := volume)
  have heq := eLpNorm_comp_measurePreserving (p := r) hm.aestronglyMeasurable
    (normalIsometry e v).measurePreserving
  change eLpNorm (fun y : (ℝ ∙ e v)ᗮ ↦
    ∫⁻ t : ℝ, f ((y : EuclideanSpace ℝ (Fin n)) + t • e v)) r volume = _
  rw [← heq]
  simp only [Function.comp_apply, coe_normalIsometry, directionXRayNorm, map_add, map_smul,
    Function.comp_def, e]

end NKBesicovitch.XRay
