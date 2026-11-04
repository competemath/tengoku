import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.SimplexLaw
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.MixtureMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The reciprocal-square tilted simplex law and its exact moments. -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter

namespace EntropyConstrainedMissingMass.Curvature

/-- Reciprocal-square tilting of the genuine simplex scale distribution.-/
noncomputable def tiltedSimplexLaw (x y z : ℝ) : Measure (ScaleInterval x y z) :=
  (simplexLaw x y z).withDensity (fun v => ENNReal.ofReal (1 / (2 * I0 x y z * (v : ℝ) ^ 2)))

/-- Integral formula for the actual tilted measure.
@isnad1 id=eq.3h4v.s7.4b99acb23c69 from=translated src=- shape=62f5e104 vocab=e0d437ec
-/
theorem integral_tiltedSimplexLaw (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (f : ScaleInterval x y z → ℝ) :
    (∫ v, f v ∂tiltedSimplexLaw x y z) =
      ∫ v : ScaleInterval x y z, (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * f v ∂simplexLaw x y z := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold tiltedSimplexLaw
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    refine Eventually.of_forall (fun v => ?_)
    dsimp only
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  · fun_prop
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- The third moment after tilting retains the original simplex mean.
@isnad1 id=eq.3h3v.s7.ae575be8f473 from=translated src=- shape=11b6e413 vocab=3d192f09
-/
theorem tiltedSimplexLaw_third_moment (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    mixtureMoment (tiltedSimplexLaw x y z) 3 = ((x + y + z) / 3) / (2 * I0 x y z) := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold mixtureMoment
  rw [integral_tiltedSimplexLaw x y z hx hy hz]
  have heq : (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * (v : ℝ) ^ 3) =
      (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z)) * (v : ℝ)) := by
    funext v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    field_simp
  rw [heq, integral_const_mul]
  change (1 / (2 * I0 x y z)) * mixtureMean (simplexLaw x y z) = _
  rw [simplexLaw_mean]
  ring

/-- The original and tilted laws have the same almost-everywhere null sets
in the direction needed to preserve nondegeneracy.
@isnad1 id=absolute.3h3v.s6.91f2a4178434 from=translated src=- shape=89ae4d8b vocab=7986c001
-/
theorem simplexLaw_absolutelyContinuous_tilted (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    simplexLaw x y z ≪ tiltedSimplexLaw x y z := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · refine Eventually.of_forall (fun v => ?_)
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

end EntropyConstrainedMissingMass.Curvature
