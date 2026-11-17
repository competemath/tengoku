import Tengoku.SingularityCompleteLean.Singularity.ParabolicOrbitHeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geodesic midpoints between opposite parabolic translates

The midpoint of z-t and z+t has real part re(z) and height
sqrt(im(z)^2+t^2). The metric segment identity is proved from the hyperbolic
cosine distance formula, so no geodesic description is assumed.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The top of the geodesic semicircle joining two opposite translates.-/
def parabolicMidpoint (z : ℍ) (t : ℝ) : ℍ :=
  ⟨⟨z.re, Real.sqrt (z.im ^ 2 + t ^ 2)⟩, Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_pos z.im_pos, sq_nonneg t])⟩

/-- Squared midpoint height.
@isnad1 id=eq.0h2v.s6.b31219e8a7cc from=translated src=- shape=8d3bf82c vocab=451460e1
-/
theorem parabolicMidpoint_im_sq (z : ℍ) (t : ℝ) :
    (parabolicMidpoint z t).im ^ 2 = z.im ^ 2 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Midpoint height grows at least as fast as the translation parameter.
@isnad1 id=le.0h2v.s4.46acbec85e50 from=translated src=- shape=55934a37 vocab=786d9c86
-/
theorem abs_le_parabolicMidpoint_im (z : ℍ) (t : ℝ) :
    |t| ≤ (parabolicMidpoint z t).im := by
  have hs := parabolicMidpoint_im_sq z t
  nlinarith [sq_abs t, (parabolicMidpoint z t).im_pos, sq_nonneg z.im]

/-- The cosine of either half-segment length is the height ratio.
@isnad1 id=eq.0h2v.s7.fc5110702588 from=translated src=- shape=b6b36f8e vocab=750c83ea
-/
theorem cosh_dist_parabolicMidpoint (z : ℍ) (t : ℝ) :
    Real.cosh (dist (upperShearMatrix t • z) (parabolicMidpoint z t)) =
      (parabolicMidpoint z t).im / z.im := by
  have hr : (upperShearMatrix t • z).re = z.re + t := by
    have h := congrArg Complex.re (upperShearMatrix_smul_coe t z)
    simpa only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re] using h
  have hi : (upperShearMatrix t • z).im = z.im := by
    have h := congrArg Complex.im (upperShearMatrix_smul_coe t z)
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero, UpperHalfPlane.coe_im] using h
  rw [UpperHalfPlane.cosh_dist', hr, hi]
  change ((z.re + t - z.re) ^ 2 + z.im ^ 2 + (parabolicMidpoint z t).im ^ 2) /
    (2 * z.im * (parabolicMidpoint z t).im) = _
  have hs := parabolicMidpoint_im_sq z t
  field_simp
  nlinarith

/-- Reversing the parameter leaves the midpoint unchanged.
@isnad1 id=eq.0h2v.s3.f368e493cb46 from=translated src=- shape=1aff131a vocab=5d075428
-/
theorem parabolicMidpoint_neg (z : ℍ) (t : ℝ) :
    parabolicMidpoint z (-t) = parabolicMidpoint z t := by
  apply UpperHalfPlane.ext
  simp [parabolicMidpoint]

/-- The constructed point lies on the metric segment joining the translates.
@isnad1 id=eq.0h2v.s9.daaa7a6c7154 from=translated src=- shape=11a388f3 vocab=2f2a126a
-/
theorem parabolicMidpoint_on_segment (z : ℍ) (t : ℝ) :
    dist (upperShearMatrix (-t) • z) (parabolicMidpoint z t) +
      dist (parabolicMidpoint z t) (upperShearMatrix t • z) =
        dist (upperShearMatrix (-t) • z) (upperShearMatrix t • z) := by
  have hl : Real.cosh (dist (upperShearMatrix (-t) • z) (parabolicMidpoint z t)) =
      (parabolicMidpoint z t).im / z.im := by
    simpa only [parabolicMidpoint_neg] using cosh_dist_parabolicMidpoint z (-t)
  have hr := cosh_dist_parabolicMidpoint z t
  have he : dist (upperShearMatrix (-t) • z) (parabolicMidpoint z t) =
      dist (upperShearMatrix t • z) (parabolicMidpoint z t) :=
    Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg (hl.trans hr.symm)
  rw [dist_comm (parabolicMidpoint z t), he, ← two_mul]
  apply Real.cosh_strictMonoOn.injOn (by exact mul_nonneg (by norm_num) dist_nonneg) dist_nonneg
  rw [Real.cosh_two_mul, Real.sinh_sq, hr, UpperHalfPlane.cosh_dist']
  have hre (v : ℝ) : (upperShearMatrix v • z).re = z.re + v := by
    have h := congrArg Complex.re (upperShearMatrix_smul_coe v z)
    simpa only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re] using h
  have him (v : ℝ) : (upperShearMatrix v • z).im = z.im := by
    have h := congrArg Complex.im (upperShearMatrix_smul_coe v z)
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero, UpperHalfPlane.coe_im] using h
  rw [hre, hre, him, him]
  have hs := parabolicMidpoint_im_sq z t
  field_simp
  nlinarith

end Singularity
