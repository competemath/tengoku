import Tengoku.SingularityCompleteLean.Singularity.CompactBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Visual measures on the full compact real boundary

The previously constructed Poisson probability measures now live on ℝ ∪ {∞}.
The genuine compact action has exact covariance; absolute continuity makes the
finite-chart pole harmless in the comparison with the earlier formulas.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Lift a finite-chart boundary measure to the compact real boundary.-/
def compactRealMeasure (ν : Measure ℝ) : Measure (OnePoint ℝ) :=
  Measure.map (fun u : ℝ => (u : OnePoint ℝ)) ν

/-- Lifting a measure through the real chart puts no mass at infinity.
@isnad1 id=eq.0h1v.s5.d0d9a4578c07 from=translated src=- shape=c1350bcb vocab=83cbd13b
-/
theorem compactRealMeasure_infty (ν : Measure ℝ) : compactRealMeasure ν {∞} = 0 := by
  rw [compactRealMeasure, Measure.map_apply OnePoint.continuous_coe.measurable
    (measurableSet_singleton _), OnePoint.coe_preimage_infty, measure_empty]

/-- The compact and finite-chart pushforwards agree for absolutely continuous measures.
@isnad1 id=eq.1h2v.s7.bbfcf2e4a650 from=translated src=- shape=5d2ae653 vocab=c1f57d8d
-/
theorem compactRealMeasure_map (ν : Measure ℝ) (hν : ν ≪ volume) (g : SL(2, ℝ)) :
    Measure.map (fun p : OnePoint ℝ => g • p) (compactRealMeasure ν) =
      compactRealMeasure (Measure.map (realBoundaryMobius g) ν) := by
  unfold compactRealMeasure
  rw [Measure.map_map (continuous_const_smul g).measurable OnePoint.continuous_coe.measurable,
    Measure.map_map OnePoint.continuous_coe.measurable (measurable_realBoundaryMobius g)]
  apply Measure.map_congr
  filter_upwards [hν.ae_le (realBoundaryMobius_denominator_ae g)] with u hu
  exact compactBoundary_smul_finite g u hu

/-- The visual Poisson probability measure on the compact boundary.-/
def compactPoissonMeasure (z : ℍ) : Measure (OnePoint ℝ) :=
  compactRealMeasure (poissonBoundaryMeasure z)

/-- The full-boundary visual measure has no atom at the omitted chart point.
@isnad1 id=eq.0h1v.s5.4dfaaa57a4c0 from=translated src=- shape=2e4c5af9 vocab=4fc6b85b
-/
theorem compactPoissonMeasure_infty (z : ℍ) : compactPoissonMeasure z {∞} = 0 :=
  compactRealMeasure_infty _

/-- Exact covariance for every matrix, with no excluded boundary points.
@isnad1 id=eq.0h2v.s8.76af663f4a6f from=translated src=- shape=f84ab328 vocab=cb2144f1
-/
theorem compactPoissonMeasure_covariance (g : SL(2, ℝ)) (z : ℍ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (compactPoissonMeasure z) =
      compactPoissonMeasure (g • z) := by
  have hac : poissonBoundaryMeasure z ≪ volume :=
    (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1
  rw [compactPoissonMeasure, compactRealMeasure_map _ hac,
    poissonBoundaryMeasure_mobius]
  rfl

end Singularity
