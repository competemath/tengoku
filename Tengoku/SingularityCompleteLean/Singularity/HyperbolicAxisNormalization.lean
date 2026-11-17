import Tengoku.SingularityCompleteLean.Singularity.AxisBallSeparation
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.ProperAction
import Tengoku.Seed.Topology.Algebra.Group.Matrix
import Tengoku.Seed.Topology.Order.IntermediateValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Placing two points on an isometric image of the vertical axis

Rotations fixing i can move any point to the vertical axis. The existence
argument is an intermediate-value argument for the real part, not an assumed
geodesic or transitivity theorem on pairs of interior points.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The determinant-one rotation family fixing i.-/
def axisRotation (t : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos t, Real.sin t; -Real.sin t, Real.cos t], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [Real.sin_sq_add_cos_sq t]⟩

/--
@isnad1 id=continuo.0h0v.s5.63fd4da4c9b4 from=translated src=- shape=8c4e1e81 vocab=186c6f67
-/
theorem continuous_axisRotation : Continuous axisRotation := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    first | exact Real.continuous_cos | exact Real.continuous_sin | exact Real.continuous_sin.neg

/--
@isnad1 id=eq.0h0v.s6.281097710370 from=translated src=- shape=98680116 vocab=eb39174d
-/
theorem axisRotation_zero : axisRotation 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [axisRotation]

/-- Every member of the rotation family fixes i.
@isnad1 id=eq.0h1v.s7.b7f86ef37498 from=translated src=- shape=d2a52af4 vocab=acf86cae
-/
theorem axisRotation_smul_I (t : ℝ) : axisRotation t • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [axisRotation, RingHom.id_apply, Algebra.algebraMap_self,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.ofReal_neg, UpperHalfPlane.coe_I]
  have hd := UpperHalfPlane.denom_ne_zero (axisRotation t) UpperHalfPlane.I
  change ((-Real.sin t : ℝ) : ℂ) * Complex.I + (Real.cos t : ℂ) ≠ 0 at hd
  rw [Complex.ofReal_neg] at hd
  rw [div_eq_iff hd]
  linear_combination (Real.sin t : ℂ) * Complex.I_sq

/-- A quarter turn acts by z ↦ -1/z.
@isnad1 id=eq.0h1v.s7.a5c8be72aaf7 from=translated src=- shape=6169a6bc vocab=28cec73c
-/
theorem axisRotation_quarter_coe (z : ℍ) :
    ((axisRotation (Real.pi / 2) • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [axisRotation, RingHom.id_apply, Algebra.algebraMap_self,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.ofReal_neg]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- The quarter turn reverses the signed vertical-axis parameter.
@isnad1 id=eq.0h1v.s7.8a5166f52113 from=translated src=- shape=b6228436 vocab=37831d4c
-/
theorem axisRotation_quarter_ray (t : ℝ) :
    axisRotation (Real.pi / 2) • verticalHeightRay UpperHalfPlane.I t =
      verticalHeightRay UpperHalfPlane.I (-t) := by
  apply UpperHalfPlane.ext
  rw [axisRotation_quarter_coe]
  apply Complex.ext
  · simp [verticalHeightRay, Complex.inv_re]
  · simp [verticalHeightRay, Complex.inv_im, Complex.normSq, Real.exp_neg]
    field_simp

/-- Some rotation fixing i moves any given point to the vertical axis.
@isnad1 id=ex.0h1v.s7.3e1eef19be4a from=translated src=- shape=ebbd9eea vocab=cd9f779c
-/
theorem exists_axisRotation_re_zero (z : ℍ) :
    ∃ t : ℝ, (axisRotation t • z).re = 0 := by
  let f : ℝ → ℝ := fun t => (axisRotation t • z).re
  have hf : Continuous f := UpperHalfPlane.continuous_re.comp (continuous_axisRotation.smul continuous_const)
  have hzero : f 0 = z.re := by simp [f, axisRotation_zero]
  have hquarter : f (Real.pi / 2) = -z.re / Complex.normSq (z : ℂ) := by
    change (((axisRotation (Real.pi / 2) • z : ℍ) : ℂ).re) = _
    rw [axisRotation_quarter_coe, Complex.neg_re, Complex.inv_re, neg_div]
    rfl
  have hnorm : 0 ≤ Complex.normSq (z : ℂ) := Complex.normSq_nonneg _
  by_cases hz : 0 ≤ z.re
  · have hh : 0 ∈ Set.Icc (f (Real.pi / 2)) (f 0) := by
      rw [hzero, hquarter]
      exact ⟨div_nonpos_of_nonpos_of_nonneg (by linarith) hnorm, hz⟩
    exact intermediate_value_univ (Real.pi / 2) 0 hf hh
  · have hh : 0 ∈ Set.Icc (f 0) (f (Real.pi / 2)) := by
      rw [hzero, hquarter]
      exact ⟨le_of_not_ge hz, div_nonneg (by linarith) hnorm⟩
    exact intermediate_value_univ 0 (Real.pi / 2) hf hh

/-- Two arbitrary interior points lie on one isometric image of the vertical
axis. The parameter difference equals their hyperbolic distance in absolute value.
@isnad1 id=ex.0h2v.s8.bc5e42eedc92 from=translated src=- shape=0753d26c vocab=2cd72fbb
-/
theorem exists_hyperbolic_axis_through (z w : ℍ) :
    ∃ (g : SL(2, ℝ)) (t : ℝ), g • UpperHalfPlane.I = z ∧
      g • verticalHeightRay UpperHalfPlane.I t = w ∧ |t| = dist z w := by
  let h := z.toSL2R
  obtain ⟨t, ht⟩ := exists_axisRotation_re_zero (h⁻¹ • w)
  let v := axisRotation t • (h⁻¹ • w)
  have hv : v = verticalHeightRay UpperHalfPlane.I (Real.log v.im) := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change v.re = 0
      exact ht
    · simp [verticalHeightRay, Real.exp_log v.im_pos]
  let g := h * (axisRotation t)⁻¹
  have hg : g • UpperHalfPlane.I = z := by
    have hi : (axisRotation t)⁻¹ • UpperHalfPlane.I = UpperHalfPlane.I := by
      exact (congrArg ((axisRotation t)⁻¹ • ·) (axisRotation_smul_I t)).symm.trans
        (by simp)
    dsimp [g, h]
    rw [mul_smul, hi, UpperHalfPlane.toSL2R_smul_I]
  have hw : g • verticalHeightRay UpperHalfPlane.I (Real.log v.im) = w := by
    rw [← hv]
    dsimp [g, v]
    simp only [mul_smul, inv_smul_smul, smul_inv_smul]
  refine ⟨g, Real.log v.im, hg, hw, ?_⟩
  rw [← hg, ← hw, dist_smul]
  have hd := verticalHeightRay_dist_eq UpperHalfPlane.I 0 (Real.log v.im)
  simpa only [verticalHeightRay_zero, zero_sub, abs_neg] using hd.symm

/-- Orient the axis so the second point has parameter equal to its distance
from the first point.
@isnad1 id=ex.0h2v.s8.5f18f27745ff from=translated src=- shape=b2c35443 vocab=44e53ee3
-/
theorem exists_oriented_hyperbolic_axis (z w : ℍ) :
    ∃ g : SL(2, ℝ), g • UpperHalfPlane.I = z ∧
      g • verticalHeightRay UpperHalfPlane.I (dist z w) = w := by
  obtain ⟨g, t, hg, hw, ht⟩ := exists_hyperbolic_axis_through z w
  by_cases hpos : 0 ≤ t
  · refine ⟨g, hg, ?_⟩
    have hd : dist z w = t := by simpa only [abs_of_nonneg hpos] using ht.symm
    rwa [hd]
  · have hneg : t ≤ 0 := le_of_not_ge hpos
    have hd : dist z w = -t := by simpa only [abs_of_nonpos hneg] using ht.symm
    refine ⟨g * axisRotation (Real.pi / 2), ?_, ?_⟩
    · rw [mul_smul, axisRotation_smul_I, hg]
    · rw [mul_smul, hd, axisRotation_quarter_ray, neg_neg, hw]

/-- Every isometric image of the parameterized vertical axis is a unit-speed
geodesic line.
@isnad1 id=isometry.0h1v.s7.ec0001c13950 from=translated src=- shape=28225ff2 vocab=62f4cbd6
-/
theorem isometry_hyperbolic_axis (g : SL(2, ℝ)) :
    Isometry (fun t : ℝ => g • verticalHeightRay UpperHalfPlane.I t) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_smul, verticalHeightRay_dist_eq, Real.dist_eq]

/-- Every pair of points is joined by one of the constructed unit-speed lines.
@isnad1 id=ex.0h2v.s5.26cc6de2da38 from=translated src=- shape=722c45b4 vocab=61a4120e
-/
theorem exists_hyperbolic_geodesic_line (z w : ℍ) :
    ∃ c : ℝ → ℍ, Isometry c ∧ c 0 = z ∧ c (dist z w) = w := by
  obtain ⟨g, hg, hw⟩ := exists_oriented_hyperbolic_axis z w
  exact ⟨fun t => g • verticalHeightRay UpperHalfPlane.I t,
    isometry_hyperbolic_axis g, by simpa only [verticalHeightRay_zero] using hg, hw⟩

end Singularity
