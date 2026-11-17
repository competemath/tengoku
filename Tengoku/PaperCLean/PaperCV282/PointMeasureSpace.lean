import Tengoku.Seed.MeasureTheory.Measure.DiracProba
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite point measures with their weak topology and its Borel sigma algebra

The underlying points are genuine finite measures. The measurable structure
is explicitly the Borel structure of the weak topology; no equality with the
separately available Giry measurable structure is presumed.
-/
namespace PaperC.V282.PointMeasureSpace

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

def PointMeasure (X : Type*) [MeasurableSpace X] := FiniteMeasure X

instance instTopologicalPointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : TopologicalSpace (PointMeasure X) :=
  inferInstanceAs (TopologicalSpace (FiniteMeasure X))

instance instMeasurablePointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : MeasurableSpace (PointMeasure X) := borel (PointMeasure X)

/--
@isnad1 id=borelspa.0h1v.s4.7e3a750319ff from=translated src=- shape=46b8a2f7 vocab=1845866d
-/
instance instBorelPointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : BorelSpace (PointMeasure X) := ⟨rfl⟩

instance instAddCommMonoidPointMeasure (X : Type*) [MeasurableSpace X] : AddCommMonoid (PointMeasure X) :=
  inferInstanceAs (AddCommMonoid (FiniteMeasure X))

/--
@isnad1 id=continuo.0h1v.s5.fa128676930d from=translated src=- shape=46b8a2f7 vocab=2b089cbe
-/
instance instContinuousAddPointMeasure (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : ContinuousAdd (PointMeasure X) :=
  inferInstanceAs (ContinuousAdd (FiniteMeasure X))

def pointDirac {X : Type*} [MeasurableSpace X] (x : X) : PointMeasure X :=
  (diracProba x).toFiniteMeasure

/--
@isnad1 id=continuo.0h1v.s4.82d225be29a9 from=translated src=- shape=1c840b92 vocab=d30ca52a
-/
theorem continuous_pointDirac {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : Continuous (pointDirac (X := X)) :=
  ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_diracProba

def fixedPointMeasure {X : Type*} [MeasurableSpace X] (n : ℕ) (marks : ℕ → X) : PointMeasure X :=
  ∑ i ∈ Finset.range n, pointDirac (marks i)

/--
@isnad1 id=continuo.0h2v.s5.6a8a13d2ca7a from=translated src=- shape=12436fc9 vocab=30874538
-/
theorem continuous_fixedPointMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (n : ℕ) : Continuous (fixedPointMeasure (X := X) n) := by
  exact continuous_finsetSum _ (fun i hi => continuous_pointDirac.comp (continuous_apply i))

def samplePointMeasure {X : Type*} [MeasurableSpace X] (sample : ℕ × (ℕ → X)) : PointMeasure X :=
  fixedPointMeasure sample.1 sample.2

/--
@isnad1 id=measurab.0h1v.s5.a07ecc5325f5 from=translated src=- shape=95815bf6 vocab=0cec42c0
-/
theorem measurable_samplePointMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X] : Measurable (samplePointMeasure (X := X)) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (continuous_fixedPointMeasure n).measurable

/--
@isnad1 id=tendsto.1h5v.s7.b5b7aeebc017 from=translated src=- shape=6d7c4bdf vocab=8752876d
-/
theorem samplePointMeasure_tendsto {X Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] (sample : ℕ × (ℕ → X)) (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ i, Tendsto (fun n => f n (sample.2 i)) atTop (𝓝 (g (sample.2 i)))) :
    Tendsto (fun n => samplePointMeasure (sample.1,fun i => f n (sample.2 i))) atTop
      (𝓝 (samplePointMeasure (sample.1,fun i => g (sample.2 i)))) := by
  unfold samplePointMeasure fixedPointMeasure
  apply tendsto_finsetSum
  intro i hi
  exact continuous_pointDirac.continuousAt.tendsto.comp (hf i)

end
end PaperC.V282.PointMeasureSpace
