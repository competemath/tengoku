/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.PolygonalQuotient
public import Tengoku

/-!
# Radial extension of circle homeomorphisms

Every `PolygonCell n` has the closed unit disk as its carrier. This file implements the radial
extension (Alexander trick) of a homeomorphism of the unit circle. The extension preserves the
norm exactly, is continuous at the origin by that norm identity, and restricts to the selected
circle homeomorphism on the boundary.

The side-count indices of the source and target cells are independent phantom parameters. A
later boundary reparameterization only needs to construct a circle homeomorphism with the desired
action on marked arcs; `PolygonCell.radialHomeomorph` then supplies the disk homeomorphism.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace Circle

/-- The direction of a nonzero complex number as a point of the unit circle. -/
noncomputable def direction (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / ‖z‖, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hz)⟩

/--
@isnad1 id=eq.1h1v.s6.60109d0c8c00 from=translated src=- shape=5df770c4 vocab=9f230508
-/
@[simp]
theorem coe_direction (z : ℂ) (hz : z ≠ 0) :
    (direction z hz : ℂ) = z / ‖z‖ :=
  rfl

/--
@isnad1 id=continuo.0h0v.s6.1420638f5bcf from=translated src=- shape=3b867c1d vocab=249dcddd
-/
theorem continuous_direction :
    Continuous (fun w : {w : ℂ // w ≠ 0} =>
      direction (w : ℂ) w.property) := by
  apply continuous_induced_rng.2
  change Continuous (fun w : {w : ℂ // w ≠ 0} =>
    (w : ℂ) / ‖(w : ℂ)‖)
  have hnorm : Continuous (fun w : {w : ℂ // w ≠ 0} =>
      (‖(w : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_subtype_val.norm
  exact continuous_subtype_val.div₀ hnorm fun w =>
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr w.property)

/-- Radially extend a circle homeomorphism to the complex plane, fixing the origin. -/
noncomputable def radialMap (h : Circle ≃ₜ Circle) (z : ℂ) : ℂ :=
  if hz : z = 0 then 0
  else (‖z‖ : ℂ) * (h (direction z hz) : ℂ)

/--
@isnad1 id=eq.0h1v.s4.2952a0253fcd from=translated src=- shape=71625799 vocab=93748ca4
-/
@[simp]
theorem radialMap_zero (h : Circle ≃ₜ Circle) :
    radialMap h 0 = 0 := by
  simp [radialMap]

/--
@isnad1 id=eq.1h2v.s7.803fecbe640a from=translated src=- shape=2af6e864 vocab=21c6b408
-/
theorem radialMap_of_ne (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    radialMap h z = (‖z‖ : ℂ) * (h (direction z hz) : ℂ) := by
  simp [radialMap, hz]

/-- Radial extension preserves distance from the origin exactly.
@isnad1 id=eq.0h2v.s4.c6d413c796d6 from=translated src=- shape=aed1972b vocab=df1ae2f4
-/
@[simp]
theorem norm_radialMap (h : Circle ≃ₜ Circle) (z : ℂ) :
    ‖radialMap h z‖ = ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [radialMap_of_ne h hz, norm_mul, Circle.norm_coe]
    simp

/--
@isnad1 id=ne.1h2v.s4.3048b4bd7f16 from=translated src=- shape=8f2a7935 vocab=93748ca4
-/
theorem radialMap_ne_zero (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    radialMap h z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_radialMap]
  exact norm_ne_zero_iff.mpr hz

/-- The direction of a radial image is the selected image direction.
@isnad1 id=eq.1h2v.s5.8671f291e818 from=translated src=- shape=54212b72 vocab=08104ffd
-/
theorem direction_radialMap (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    direction (radialMap h z) (radialMap_ne_zero h hz) =
      h (direction z hz) := by
  apply Subtype.ext
  rw [coe_direction, radialMap_of_ne h hz]
  simp only [norm_mul, Circle.norm_coe, mul_one, norm_real,
    Real.norm_eq_abs, abs_norm]
  field_simp [norm_ne_zero_iff.mpr hz]

/-- Extending the inverse circle homeomorphism gives the inverse radial map.
@isnad1 id=eq.0h2v.s4.712583b27753 from=translated src=- shape=7450e864 vocab=95fe11ad
-/
theorem radialMap_symm_apply (h : Circle ≃ₜ Circle) (z : ℂ) :
    radialMap h.symm (radialMap h z) = z := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [radialMap_of_ne h.symm (radialMap_ne_zero h hz),
      direction_radialMap h hz, h.symm_apply_apply, norm_radialMap,
      coe_direction]
    field_simp [norm_ne_zero_iff.mpr hz]

/--
@isnad1 id=continuo.0h1v.s5.40598ce2b7f4 from=translated src=- shape=cfd42336 vocab=f89dc32d
-/
theorem continuousAt_radialMap_zero (h : Circle ≃ₜ Circle) :
    ContinuousAt (radialMap h) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro z hz
  rw [radialMap_zero, dist_zero_right, norm_radialMap,
    ← dist_zero_right]
  exact hz

/--
@isnad1 id=continuo.1h2v.s5.be7ee01ca12f from=translated src=- shape=3c318702 vocab=f89dc32d
-/
theorem continuousAt_radialMap_of_ne (h : Circle ≃ₜ Circle)
    {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (radialMap h) z := by
  have hrestrict :
      Continuous (fun w : {w : ℂ // w ≠ 0} => radialMap h w) := by
    have heq :
        (fun w : {w : ℂ // w ≠ 0} => radialMap h w) =
          fun w : {w : ℂ // w ≠ 0} => (‖(w : ℂ)‖ : ℂ) *
            (h (direction (w : ℂ) w.property) : ℂ) := by
      funext w
      exact radialMap_of_ne h w.property
    rw [heq]
    have hnorm : Continuous (fun w : {w : ℂ // w ≠ 0} =>
        (‖(w : ℂ)‖ : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_subtype_val.norm
    exact hnorm.mul
      (continuous_subtype_val.comp
        (h.continuous.comp continuous_direction))
  have hOn : ContinuousOn (radialMap h) ({0}ᶜ : Set ℂ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hrestrict
  exact (hOn z hz).continuousAt (isOpen_compl_singleton.mem_nhds hz)

/--
@isnad1 id=continuo.0h1v.s5.a8f290dc06e7 from=translated src=- shape=d8239103 vocab=ec9fc058
-/
theorem continuous_radialMap (h : Circle ≃ₜ Circle) :
    Continuous (radialMap h) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact continuousAt_radialMap_zero h
  · exact continuousAt_radialMap_of_ne h hz

/-- On the unit circle, radial extension is exactly the original homeomorphism.
@isnad1 id=eq.0h2v.s7.0606b6a4afee from=translated src=- shape=b87c3014 vocab=7962cc76
-/
@[simp]
theorem radialMap_coe (h : Circle ≃ₜ Circle) (z : Circle) :
    radialMap h (z : ℂ) = (h z : ℂ) := by
  rw [radialMap_of_ne h z.coe_ne_zero, z.norm_coe]
  have hdirection : direction (z : ℂ) z.coe_ne_zero = z := by
    apply Circle.ext
    rw [coe_direction, z.norm_coe]
    simp
  rw [hdirection]
  simp

end Circle

namespace PolygonCell

/-- Radially extend a circle homeomorphism between closed polygon-cell carriers. -/
noncomputable def radialHomeomorph {n m : ℕ} (h : Circle ≃ₜ Circle) :
    PolygonCell n ≃ₜ PolygonCell m where
  toFun z := ⟨Circle.radialMap h z.val, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_radialMap]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  invFun z := ⟨Circle.radialMap h.symm z.val, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_radialMap]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  left_inv := by
    intro z
    apply PolygonCell.ext
    exact Circle.radialMap_symm_apply h z.val
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact Circle.radialMap_symm_apply h.symm z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact Circle.continuous_radialMap h |>.comp PolygonCell.continuous_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact Circle.continuous_radialMap h.symm |>.comp PolygonCell.continuous_val

/--
@isnad1 id=eq.0h4v.s6.ed92397df8b9 from=translated src=- shape=0a40a511 vocab=49fec09c
-/
@[simp]
theorem radialHomeomorph_apply_val {n m : ℕ} (h : Circle ≃ₜ Circle)
    (z : PolygonCell n) :
    (radialHomeomorph (n := n) (m := m) h z).val =
      Circle.radialMap h z.val :=
  rfl

/-- The radial cell homeomorphism restricts to the selected circle homeomorphism.
@isnad1 id=eq.0h4v.s7.7bba8def3a2b from=translated src=- shape=c47bae8c vocab=ac235424
-/
@[simp]
theorem radialHomeomorph_ofCircle {n m : ℕ} (h : Circle ≃ₜ Circle)
    (z : Circle) :
    radialHomeomorph h (ofCircle n z) = ofCircle m (h z) := by
  apply PolygonCell.ext
  exact Circle.radialMap_coe h z

end PolygonCell

end LeanEval.Topology.ClassificationOfSurfaces
