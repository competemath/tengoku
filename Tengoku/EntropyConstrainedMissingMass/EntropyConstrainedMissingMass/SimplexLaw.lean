import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.SimplexIntegrals
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A genuine probability law for the uniform-simplex parametrization. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Topology unitInterval

namespace EntropyConstrainedMissingMass
namespace Curvature

abbrev SimplexSquare := I × I

/-- Jacobian weight of the square parametrization of the uniform simplex.-/
def simplexWeight (q : SimplexSquare) : ℝ := 2 * (1 - (q.1 : ℝ))

/-- The square-coordinate probability measure inducing uniform simplex coordinates.-/
noncomputable def simplexMeasure : Measure SimplexSquare :=
  volume.withDensity (fun q => ENNReal.ofReal (simplexWeight q))

/--
@isnad1 id=le.0h1v.s3.15156acfad75 from=translated src=- shape=b9369acb vocab=20689f0d
-/
theorem simplexWeight_nonneg (q : SimplexSquare) : 0 ≤ simplexWeight q := by
  unfold simplexWeight
  have h := q.1.property.2
  positivity

/-- Integrals on the canonical unit-interval probability space are ordinary interval integrals.
@isnad1 id=eq.0h1v.s6.b3acfa6c2331 from=translated src=- shape=67da4e88 vocab=7ec4fbae
-/
theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ u : I, f (u : ℝ)) = ∫ u in (0 : ℝ)..1, f u := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

private theorem continuous_simplexWeight : Continuous simplexWeight := by
  unfold simplexWeight
  fun_prop

private theorem integrable_simplexWeight : Integrable simplexWeight :=
  continuous_simplexWeight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The Jacobian weight integrates to one.
@isnad1 id=eq.0h0v.s5.265a60f54c01 from=translated src=- shape=403ebd4d vocab=d2d9a222
-/
theorem integral_simplexWeight : (∫ q : SimplexSquare, simplexWeight q) = 1 := by
  change (∫ q : SimplexSquare, simplexWeight q ∂(volume.prod volume)) = 1
  rw [integral_prod _ integrable_simplexWeight]
  simp only [simplexWeight, integral_const, probReal_univ, one_smul]
  rw [integral_unitInterval (fun u : ℝ => 2 * (1 - u))]
  have hi : IntervalIntegrable (fun u : ℝ => u) volume 0 1 :=
    continuous_id.intervalIntegrable (0 : ℝ) 1
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const hi]
  norm_num

/-- Integration against the simplex law is integration with its nonnegative Jacobian weight.
@isnad1 id=eq.0h1v.s6.7b9fc9470359 from=translated src=- shape=27d236e2 vocab=314eecf0
-/
theorem integral_simplexMeasure (f : SimplexSquare → ℝ) :
    (∫ q, f q ∂simplexMeasure) = ∫ q, simplexWeight q * f q := by
  unfold simplexMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by
      dsimp only
      rw [ENNReal.toReal_ofReal (simplexWeight_nonneg q), smul_eq_mul])
  · exact continuous_simplexWeight.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- Weighted Fubini on the simplex square, for continuous functions.
@isnad1 id=eq.1h1v.s8.48e762c0adc3 from=translated src=- shape=c4b50319 vocab=d032a11c
-/
theorem integral_simplexMeasure_eq_iterated (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun q : SimplexSquare => f q.1 q.2)) :
    (∫ q : SimplexSquare, f q.1 q.2 ∂simplexMeasure) =
      ∫ u in (0 : ℝ)..1, 2 * (1 - u) * ∫ v in (0 : ℝ)..1, f u v := by
  rw [integral_simplexMeasure]
  have hi : Integrable (fun q : SimplexSquare => simplexWeight q * f q.1 q.2) :=
    (continuous_simplexWeight.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ q : SimplexSquare, simplexWeight q * f q.1 q.2 ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  simp only [simplexWeight, integral_const_mul]
  simp_rw [integral_unitInterval]
  exact integral_unitInterval (fun u : ℝ => 2 * (1 - u) * ∫ v in (0 : ℝ)..1, f u v)

/-- The barycentric coordinates are nonnegative and sum to one under this law.
@isnad1 id=and.0h1v.s8.dc34e30f5669 from=translated src=- shape=59d9f979 vocab=0149f4d9
-/
theorem simplex_coordinates (q : SimplexSquare) :
    0 ≤ (q.1 : ℝ) ∧ 0 ≤ (1 - (q.1 : ℝ)) * (q.2 : ℝ) ∧
      0 ≤ (1 - (q.1 : ℝ)) * (1 - (q.2 : ℝ)) ∧
      (q.1 : ℝ) + (1 - (q.1 : ℝ)) * (q.2 : ℝ) +
        (1 - (q.1 : ℝ)) * (1 - (q.2 : ℝ)) = 1 := by
  have hu0 := q.1.property.1
  have hu1 := q.1.property.2
  have hv0 := q.2.property.1
  have hv1 := q.2.property.2
  refine ⟨hu0, by positivity, by positivity, ?_⟩
  ring

/-- The interval containing all simplex scales.-/
abbrev ScaleInterval (x y z : ℝ) := Icc (min x (min y z)) (max x (max y z))

/-- The simplex scale as an element of its compact range interval.-/
def simplexScale (x y z : ℝ) (q : SimplexSquare) : ScaleInterval x y z :=
  ⟨simplexValue x y z q.1 q.2, simplexValue_mem x y z _ _ q.1 q.2
    ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
    q.1.property q.2.property⟩

/--
@isnad1 id=continuo.0h3v.s6.bd60e83089e4 from=translated src=- shape=70165958 vocab=91bd8552
-/
theorem continuous_simplexScale (x y z : ℝ) : Continuous (simplexScale x y z) := by
  apply Continuous.subtype_mk
  unfold simplexValue
  fun_prop

/-- The law of the affine simplex scale.-/
noncomputable def simplexLaw (x y z : ℝ) : Measure (ScaleInterval x y z) :=
  simplexMeasure.map (simplexScale x y z)

/-- The lower endpoint of the scale interval is positive for a positive triple.
@isnad1 id=lt.3h3v.s5.1ecb6945e47f from=translated src=- shape=3377e866 vocab=04058b2f
-/
theorem scaleInterval_lower_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < min x (min y z) := lt_min hx (lt_min hy hz)

/-- The exact pushforward integration formula.
@isnad1 id=eq.1h4v.s7.92c0d6fd5cd5 from=translated src=- shape=13c257ff vocab=8340d0dd
-/
theorem integral_simplexLaw (x y z : ℝ) (f : ScaleInterval x y z → ℝ) (hf : Continuous f) :
    (∫ v, f v ∂simplexLaw x y z) = ∫ q, f (simplexScale x y z q) ∂simplexMeasure := by
  exact integral_map (continuous_simplexScale x y z).measurable.aemeasurable
    hf.aestronglyMeasurable

/-- First moment of the actual simplex probability law.
@isnad1 id=eq.0h3v.s6.25559b1422de from=translated src=- shape=63b9dba9 vocab=d4df360e
-/
theorem simplexLaw_mean (x y z : ℝ) : mixtureMean (simplexLaw x y z) = (x + y + z) / 3 := by
  unfold mixtureMean
  rw [integral_simplexLaw x y z _ continuous_subtype_val]
  change (∫ q : SimplexSquare, simplexValue x y z q.1 q.2 ∂simplexMeasure) = _
  rw [integral_simplexMeasure_eq_iterated (simplexValue x y z) (by unfold simplexValue; fun_prop),
    simplex_first_moment]

/-- Second moment of the actual simplex probability law.
@isnad1 id=eq.0h3v.s7.3a72dac3f8a8 from=translated src=- shape=eff67c7d vocab=ac4bcc82
-/
theorem simplexLaw_second_moment (x y z : ℝ) :
    (∫ v : ScaleInterval x y z, (v : ℝ) ^ 2 ∂simplexLaw x y z) =
      (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z) / 6 := by
  rw [integral_simplexLaw x y z _ (by fun_prop)]
  change (∫ q : SimplexSquare, (simplexValue x y z q.1 q.2) ^ 2 ∂simplexMeasure) = _
  rw [integral_simplexMeasure_eq_iterated (fun u v => (simplexValue x y z u v) ^ 2)
    (by unfold simplexValue; fun_prop), simplex_second_moment]

end Curvature
end EntropyConstrainedMissingMass
