/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Tengoku

/-!
# Doubling geometry for parabolic volume

The parabolic metric has homogeneous dimension five.  The lemmas below record
the corresponding scaling of the spatial balls and parabolic cylinders, then
use the cylinder/metric-ball comparison from `Basic` to provide the doubling
instance required by metric covering arguments.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Linear spatial dilation used in the parabolic doubling calculation. -/
def doublingVec3ScaleLinear (a : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  a • LinearMap.id

private lemma vec3ScaleLinear_apply (a : ℝ) (v : Vec3) :
    doublingVec3ScaleLinear a v = a • v := by
  rfl

private lemma vec3ScaleLinear_det (a : ℝ) :
    LinearMap.det (doublingVec3ScaleLinear a) = a ^ 3 := by
  simp [doublingVec3ScaleLinear, LinearMap.det_smul, LinearMap.det_id]

lemma volume_vec3Ball_scale {a r : ℝ} (ha : 0 < a) :
    volume (vec3Ball 0 (a * r)) = ENNReal.ofReal (a ^ 3) * volume (vec3Ball 0 r) := by
  let f := doublingVec3ScaleLinear a⁻¹
  have hdet : LinearMap.det f ≠ 0 := by
    rw [show f = doublingVec3ScaleLinear a⁻¹ by rfl, vec3ScaleLinear_det]
    exact pow_ne_zero 3 (inv_ne_zero ha.ne')
  have hpre : (f : Vec3 → Vec3) ⁻¹' vec3Ball 0 r = vec3Ball 0 (a * r) := by
    ext y
    change vec3EuclideanNorm (f y - 0) < r ↔ vec3EuclideanNorm (y - 0) < a * r
    rw [sub_zero, sub_zero, vec3ScaleLinear_apply, vec3EuclideanNorm_smul,
      abs_of_pos (inv_pos.mpr ha)]
    constructor
    · intro h
      calc
        vec3EuclideanNorm y = a * (a⁻¹ * vec3EuclideanNorm y) := by
          field_simp [ha.ne']
        _ < a * r := mul_lt_mul_of_pos_left h ha
    · intro h
      have h' := mul_lt_mul_of_pos_left h (inv_pos.mpr ha)
      calc
        a⁻¹ * vec3EuclideanNorm y < a⁻¹ * (a * r) := h'
        _ = r := by field_simp [ha.ne']
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f) hdet
  have hmeasure := congrArg (fun μ : Measure Vec3 => μ (vec3Ball 0 r)) hmap
  rw [Measure.map_apply (f.continuous_of_finiteDimensional.measurable)
    (vec3Ball_measurable 0 r), hpre, Measure.smul_apply] at hmeasure
  rw [vec3ScaleLinear_det] at hmeasure
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  simpa [f, abs_of_pos (inv_pos.mpr ha), abs_of_pos ha, inv_pow, ha.ne',
    ENNReal.ofReal_inv_of_pos ha3, ENNReal.ofReal_pow ha.le] using hmeasure

lemma volume_parabolicCylinder_radius_scale {x : Vec3} {t r a : ℝ} (ha : 0 < a) :
    volume (parabolicCylinder x t (a * r)) =
      ENNReal.ofReal (a ^ 5) * volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder, volume_parabolicCylinder,
    volume_vec3Ball x (a * r), volume_vec3Ball x r, volume_vec3Ball_scale ha, mul_pow,
    ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 2)]
  calc
    _ = (ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (a ^ 2)) *
        (volume (vec3Ball 0 r) * ENNReal.ofReal (r ^ 2)) := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 3), ← pow_add]

lemma volume_parabolicCylinder_time (x : Vec3) (t₁ t₂ r : ℝ) :
    volume (parabolicCylinder x t₁ r) = volume (parabolicCylinder x t₂ r) := by
  rw [volume_parabolicCylinder, volume_parabolicCylinder]

end CKN.Foundation.Parabolic
