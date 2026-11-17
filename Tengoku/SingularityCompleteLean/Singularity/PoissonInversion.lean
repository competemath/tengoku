import Tengoku.SingularityCompleteLean.Singularity.PoissonMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inversion covariance of the Poisson measure

The finite real-chart inversion is u ↦ -1/u, with its value at zero irrelevant
to these absolutely continuous measures. The Jacobian is proved off zero and
the exceptional singleton is removed using its zero Lebesgue measure.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

def boundaryInversion (u : ℝ) : ℝ := -u⁻¹

/--
@isnad1 id=measurab.0h0v.s2.aa0fa09995c7 from=translated src=- shape=e3d48bcb vocab=6033df3a
-/
theorem measurable_boundaryInversion : Measurable boundaryInversion := by
  unfold boundaryInversion
  fun_prop

/--
@isnad1 id=involuti.0h0v.s1.0ae75d837ad6 from=translated src=- shape=25b03439 vocab=11f6df86
-/
theorem boundaryInversion_involutive : Function.Involutive boundaryInversion := by
  intro u
  simp [boundaryInversion]

/--
@isnad1 id=eq.0h0v.s5.f4ffaebbfae8 from=translated src=- shape=94498aa2 vocab=a069c130
-/
theorem boundaryInversion_image_ne_zero : boundaryInversion '' ({0}ᶜ : Set ℝ) = {0}ᶜ := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [boundaryInversion] using hv
  · intro hu
    refine ⟨boundaryInversion u, ?_, boundaryInversion_involutive u⟩
    simpa [boundaryInversion] using hu

/--
@isnad1 id=hasderiv.1h1v.s5.6ea9e39f671b from=translated src=- shape=3c80e79c vocab=893a90b5
-/
theorem hasDerivAt_boundaryInversion {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt boundaryInversion ((u ^ 2)⁻¹) u := by
  change HasDerivAt (fun v : ℝ => -v⁻¹) ((u ^ 2)⁻¹) u
  convert! (hasDerivAt_inv hu).neg using 1
  simp

/-- The inverse-square Jacobian transports Lebesgue measure through inversion.
@isnad1 id=eq.0h0v.s5.1b713dc271e0 from=translated src=- shape=d6686a73 vocab=86282e8c
-/
theorem boundaryInversion_jacobian_map :
    Measure.map boundaryInversion (volume.withDensity (fun u : ℝ => ENNReal.ofReal ((u ^ 2)⁻¹))) =
      volume := by
  have hz : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
  have hr : (volume : Measure ℝ).restrict {0}ᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem (by simpa using hz)
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh measurable_boundaryInversion,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun u => h (boundaryInversion u)) from hh.comp measurable_boundaryInversion)]
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul
    (measurableSet_singleton (0 : ℝ)).compl
    (fun u hu => (hasDerivAt_boundaryInversion (by simpa using hu)).hasDerivWithinAt)
    boundaryInversion_involutive.injective.injOn h
  rw [boundaryInversion_image_ne_zero, hr] at hj
  simpa only [Pi.mul_apply, abs_inv, abs_of_nonneg (sq_nonneg (_ : ℝ))] using hj.symm

/-- The distance-squared denominator identity behind inversion covariance.
@isnad1 id=eq.2h3v.s8.720d0a524c51 from=translated src=- shape=5dcfa7bd vocab=088f92d5
-/
theorem poisson_inversion_denominator (x : ℝ) {y u : ℝ} (hy : 0 < y) (hu : u ≠ 0) :
    (boundaryInversion u - (-x / (x ^ 2 + y ^ 2))) ^ 2 + (y / (x ^ 2 + y ^ 2)) ^ 2 =
      ((u - x) ^ 2 + y ^ 2) / (u ^ 2 * (x ^ 2 + y ^ 2)) := by
  have hr : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold boundaryInversion
  field_simp [hu, hr]
  ring

/-- The Poisson kernel transforms with the inverse-square boundary Jacobian.
@isnad1 id=eq.2h3v.s7.9b350bf9c6c4 from=translated src=- shape=6bf4e4a0 vocab=cc07f160
-/
theorem halfPlanePoisson_inversion (x : ℝ) {y : ℝ} (hy : 0 < y)
    {u : ℝ} (hu : u ≠ 0) :
    (u ^ 2)⁻¹ * halfPlanePoisson (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2))
      (boundaryInversion u) = halfPlanePoisson x y u := by
  unfold halfPlanePoisson
  rw [poisson_inversion_denominator x hy hu]
  have hr : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd : (u - x) ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hu, hr, hd]

/-- Inversion of the boundary transports the Poisson probability measure to
the measure at the inverted upper-half-plane point.
@isnad1 id=eq.1h2v.s7.2fd4f020b440 from=translated src=- shape=53aafa48 vocab=62a4617f
-/
theorem halfPlanePoissonMeasure_inversion (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Measure.map boundaryInversion (halfPlanePoissonMeasure x y) =
      halfPlanePoissonMeasure (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2)) := by
  let P := halfPlanePoisson (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2))
  have hP : Measurable P := measurable_halfPlanePoisson _ _
  have h := map_withDensity_comp boundaryInversion measurable_boundaryInversion
    (volume.withDensity (fun u : ℝ => ENNReal.ofReal ((u ^ 2)⁻¹)))
    (fun u => ENNReal.ofReal (P u)) hP.ennreal_ofReal
  rw [boundaryInversion_jacobian_map, ← withDensity_mul _ (by fun_prop)
    (hP.ennreal_ofReal.comp measurable_boundaryInversion)] at h
  have heq : (volume : Measure ℝ).withDensity
      ((fun u => ENNReal.ofReal ((u ^ 2)⁻¹)) * (fun u => ENNReal.ofReal (P u)) ∘ boundaryInversion) =
      halfPlanePoissonMeasure x y := by
    apply withDensity_congr_ae
    have hz : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
    filter_upwards [hz] with u hu
    change ENNReal.ofReal ((u ^ 2)⁻¹) * ENNReal.ofReal (P (boundaryInversion u)) = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _))]
    exact congrArg ENNReal.ofReal (halfPlanePoisson_inversion x hy hu)
  rw [heq] at h
  exact h

end Singularity
