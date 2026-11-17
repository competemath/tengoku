import Tengoku.SingularityCompleteLean.Singularity.RealBoundaryTransport
import Tengoku.SingularityCompleteLean.Singularity.CompactPoissonMeasure
import Tengoku.SingularityCompleteLean.Singularity.PoissonDomination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Passing from the compact hitting law to its finite real chart

A measurable inverse of the finite chart transfers measures on ℝ ∪ {∞} to ℝ.
Zero mass at infinity gives exact reconstruction. Absolute continuity or a
bounded-density comparison with a compact Poisson measure supplies this condition,
transfers the Poisson bound, and identifies all finite-chart Möbius pushforwards.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The finite real chart is a measurable embedding.
@isnad1 id=measurab.0h0v.s4.d0d59b97e7d3 from=translated src=- shape=7cee391e vocab=9acde27c
-/
theorem measurableEmbedding_realChart : MeasurableEmbedding (fun x : ℝ => (x : OnePoint ℝ)) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

/-- A measurable coordinate on the finite chart, extended at infinity.-/
def finiteBoundaryCoordinate : OnePoint ℝ → ℝ := measurableEmbedding_realChart.invFun

/--
@isnad1 id=measurab.0h0v.s3.f61489b574fb from=translated src=- shape=d7985952 vocab=6d6e9294
-/
theorem measurable_finiteBoundaryCoordinate : Measurable finiteBoundaryCoordinate :=
  measurableEmbedding_realChart.measurable_invFun

/-- The coordinate recovers every finite real point exactly.
@isnad1 id=eq.0h1v.s3.3f7e843de122 from=translated src=- shape=8e255869 vocab=9ab182b8
-/
theorem finiteBoundaryCoordinate_coe (x : ℝ) : finiteBoundaryCoordinate (x : OnePoint ℝ) = x :=
  measurableEmbedding_realChart.leftInverse_invFun x

/-- Express a compact-boundary measure in the finite real chart.-/
def finiteBoundaryMeasure (ν : Measure (OnePoint ℝ)) : Measure ℝ :=
  Measure.map finiteBoundaryCoordinate ν

/-- Coordinate transport preserves probabilities.
@isnad1 id=isprobab.0h1v.s4.0f10edc557db from=translated src=- shape=b661a782 vocab=d7877632
-/
theorem finiteBoundaryMeasure_probability (ν : Measure (OnePoint ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finiteBoundaryMeasure ν) :=
  (Measure.isProbabilityMeasure_map_iff measurable_finiteBoundaryCoordinate.aemeasurable).mpr
    inferInstance

/-- Lifting a real measure and then taking its finite chart changes nothing.
@isnad1 id=eq.0h1v.s3.d64873ddc965 from=translated src=- shape=e9e6e124 vocab=c69f8e05
-/
theorem finiteBoundaryMeasure_compactRealMeasure (ν : Measure ℝ) :
    finiteBoundaryMeasure (compactRealMeasure ν) = ν := by
  rw [finiteBoundaryMeasure, compactRealMeasure,
    Measure.map_map measurable_finiteBoundaryCoordinate OnePoint.continuous_coe.measurable]
  have he : finiteBoundaryCoordinate ∘ (fun x : ℝ => (x : OnePoint ℝ)) = id :=
    funext finiteBoundaryCoordinate_coe
  rw [he, Measure.map_id]

/-- Zero mass at infinity is exactly what is needed for reconstruction in the finite chart.
@isnad1 id=eq.1h1v.s6.75eaa6e906a9 from=translated src=- shape=c9e888ca vocab=fe293c79
-/
theorem finiteBoundaryMeasure_reconstruct (ν : Measure (OnePoint ℝ)) (hinfty : ν {∞} = 0) :
    compactRealMeasure (finiteBoundaryMeasure ν) = ν := by
  have hae : ∀ᵐ p ∂ν, p ≠ (∞ : OnePoint ℝ) := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_eq_eq_singleton] using hinfty
  rw [compactRealMeasure, finiteBoundaryMeasure,
    Measure.map_map OnePoint.continuous_coe.measurable measurable_finiteBoundaryCoordinate]
  calc
    _ = Measure.map id ν := by
      apply Measure.map_congr
      filter_upwards [hae] with p hp
      cases p with
      | infty => exact (hp rfl).elim
      | coe x => exact congrArg (fun y : ℝ => (y : OnePoint ℝ)) (finiteBoundaryCoordinate_coe x)
    _ = ν := Measure.map_id

/-- Absolute continuity with a visual measure rules out mass at infinity.
@isnad1 id=eq.1h2v.s6.ac35d366d010 from=translated src=- shape=c0516574 vocab=7551e09a
-/
theorem compactPoisson_ac_infty (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z) : ν {∞} = 0 :=
  hac (compactPoissonMeasure_infty z)

/-- Compact visual absolute continuity supplies Lebesgue absolute continuity in the real chart.
@isnad1 id=absolute.1h2v.s5.a90ca10415a5 from=translated src=- shape=8de8910a vocab=78f32403
-/
theorem finiteBoundaryMeasure_absolutelyContinuous (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z) : finiteBoundaryMeasure ν ≪ volume := by
  have h := hac.map measurable_finiteBoundaryCoordinate
  change finiteBoundaryMeasure ν ≪ finiteBoundaryMeasure (compactRealMeasure (poissonBoundaryMeasure z)) at h
  rw [finiteBoundaryMeasure_compactRealMeasure] at h
  exact h.trans (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1

/-- The chart of a compact translate is the existing real Möbius pushforward.
@isnad1 id=eq.1h3v.s8.26106a7511d3 from=translated src=- shape=9eb44ac8 vocab=23e7b33b
-/
theorem finiteBoundaryMeasure_map (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z) (g : SL(2, ℝ)) :
    finiteBoundaryMeasure (Measure.map (fun p : OnePoint ℝ => g • p) ν) =
      Measure.map (realBoundaryMobius g) (finiteBoundaryMeasure ν) := by
  have hrec := finiteBoundaryMeasure_reconstruct ν (compactPoisson_ac_infty ν z hac)
  calc
    _ = finiteBoundaryMeasure (Measure.map (fun p : OnePoint ℝ => g • p)
        (compactRealMeasure (finiteBoundaryMeasure ν))) := by rw [hrec]
    _ = _ := by
      rw [compactRealMeasure_map _ (finiteBoundaryMeasure_absolutelyContinuous ν z hac),
        finiteBoundaryMeasure_compactRealMeasure]

end Singularity
