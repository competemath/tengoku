import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportGeometry
import Tengoku.Seed.MeasureTheory.Measure.ProbabilityMeasure
import Tengoku.Seed.MeasureTheory.Measure.RegularityCompacts
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reservoir measures at the collapsed boundary

An interior measure is augmented by a boundary atom to reach a chosen finite
capacity. Its interior restriction is preserved, and its distance-to-boundary
moment is exactly the input diagonal persistence moment, including infinite
values. Normalization gives a probability measure. Paired capacities explicitly
dominate the sum of the two original masses.
-/

noncomputable section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace TDA.Persistence.BoundaryTransport

/-- The p-th power of distance to the collapsed boundary, as an extended nonnegative
integrand.-/
def boundaryMomentIntegrand (p : ℝ) (x : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (dist x Space.boundary ^ p)

/-- Add exactly enough mass at the collapsed boundary to reach reservoir capacity `R`.-/
def reservoirMeasure (μ : Measure Interior) (R : ℝ≥0∞) : Measure Space :=
  μ.map Space.point + (R - μ Set.univ) • Measure.dirac Space.boundary

theorem reservoirMeasure_apply_interior (μ : Measure Interior) (R : ℝ≥0∞)
    {s : Set Space} (hs : MeasurableSet s) (hb : Space.boundary ∉ s) :
    reservoirMeasure μ R s = μ (Space.point ⁻¹' s) := by
  rw [reservoirMeasure, Measure.add_apply, Measure.map_apply continuous_point.measurable hs,
    Measure.smul_apply]
  simp [Measure.dirac_apply, hb]

theorem reservoirMeasure_mass (μ : Measure Interior) (R : ℝ≥0∞)
    (hmass : μ Set.univ ≤ R) :
    reservoirMeasure μ R Set.univ = R := by
  rw [reservoirMeasure, Measure.add_apply, Measure.map_apply continuous_point.measurable
    MeasurableSet.univ, Measure.smul_apply, smul_eq_mul]
  simp only [preimage_univ, Measure.dirac_apply' Space.boundary MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  simpa only [add_comm] using (add_tsub_cancel_of_le hmass)

theorem reservoirMeasure_restrict_interior (μ : Measure Interior) (R : ℝ≥0∞) :
    (reservoirMeasure μ R).restrict (Set.range Space.point) = μ.map Space.point := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs]
  have hb : Space.boundary ∉ s ∩ Set.range Space.point := by
    rintro ⟨_, x, hx⟩
    cases hx
  rw [reservoirMeasure_apply_interior μ R
    (hs.inter measurableEmbedding_point.measurableSet_range) hb,
    Measure.map_apply continuous_point.measurable hs]
  simp [preimage_inter, preimage_range]

theorem reservoirMeasure_boundary_moment (μ : Measure Interior) (R : ℝ≥0∞)
    (p : ℝ) (hp : 0 < p) :
    ∫⁻ x, boundaryMomentIntegrand p x ∂reservoirMeasure μ R =
      ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
  have hp0 : 0 ≤ p := hp.le
  have hdist : Continuous (fun x : Space => dist x Space.boundary) := by
    exact continuous_dist.comp (continuous_id.prodMk continuous_const)
  have hf : Measurable (boundaryMomentIntegrand p) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_rpow_const hp0).comp hdist).measurable
  rw [reservoirMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_map hf continuous_point.measurable]
  simp [boundaryMomentIntegrand, dist_point_boundary,
    Real.zero_rpow hp.ne']

@[simp] theorem reservoirMeasure_zero (R : ℝ≥0∞) :
    reservoirMeasure (0 : Measure Interior) R = R • Measure.dirac Space.boundary := by
  simp [reservoirMeasure]

/-- Normalize a finite positive reservoir into a probability measure.-/
def normalizedReservoirMeasure (μ : Measure Interior) (R : ℝ≥0∞) : Measure Space :=
  R⁻¹ • reservoirMeasure μ R

theorem normalizedReservoirMeasure_mass (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (hmass : μ Set.univ ≤ R) :
    normalizedReservoirMeasure μ R Set.univ = 1 := by
  rw [normalizedReservoirMeasure, Measure.smul_apply, smul_eq_mul,
    reservoirMeasure_mass μ R hmass]
  exact ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne

theorem normalizedReservoirMeasure_isProbability (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (hmass : μ Set.univ ≤ R) :
    IsProbabilityMeasure (normalizedReservoirMeasure μ R) :=
  ⟨normalizedReservoirMeasure_mass μ R hRtop hRpos hmass⟩

def normalizedReservoirProbability (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) (hmass : μ Set.univ ≤ R) : ProbabilityMeasure Space :=
  ⟨normalizedReservoirMeasure μ R,
    normalizedReservoirMeasure_isProbability μ R hRtop hRpos hmass⟩

@[simp] theorem coe_normalizedReservoirProbability (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) (hmass : μ Set.univ ≤ R) :
    (normalizedReservoirProbability μ R hRtop hRpos hmass : Measure Space) =
      normalizedReservoirMeasure μ R := rfl

end TDA.Persistence.BoundaryTransport
