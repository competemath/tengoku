/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Tengoku.LeanPool.LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure`

Pushforward measures on the model space arising from charts.

For chart-based Sobolev spaces on a manifold `M`, it is convenient to transport the ambient measure
on `M` to a measure on the model space `E` using `extChartAt`. This file defines the resulting
measures and records basic finiteness instances needed by the Euclidean Sobolev baseline.
-/

@[expose] public section

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open scoped _root_.Manifold MeasureTheory Topology
open MeasureTheory

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceChartMeasure : MeasurableSpace M := borel M
/--
@isnad1 id=borelspa.0h1v.s3.460708b22f47 from=translated src=- shape=c6850a32 vocab=723886c8
-/
local instance instBorelSpaceChartMeasure : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceChartMeasure1 : MeasurableSpace E := borel E
/--
@isnad1 id=borelspa.0h1v.s4.e7f0015bcad1 from=translated src=- shape=c6850a32 vocab=97166edf
-/
local instance instBorelSpaceChartMeasure1 : BorelSpace E := ⟨rfl⟩
/--
@isnad1 id=opensmea.0h1v.s4.671960873e7a from=translated src=- shape=c6850a32 vocab=1f1877c2
-/
local instance instOpensMeasurableSpaceChartMeasure : OpensMeasurableSpace E := by infer_instance

/-- Any finite measure is finite on compact sets.
@isnad1 id=isfinite.0h2v.s4.caae59592b9e from=translated src=- shape=f15eaebe vocab=83ad7d79
-/
lemma isFiniteMeasureOnCompacts_of_isFiniteMeasure {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun K _hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top μ Set.univ)⟩

namespace FiniteChartData

variable (d : FiniteChartData (H := H) (M := M) I)

/-!
## Chart measures

Given a measure `μ` on `M`, each chart center `d.center i` yields a pushforward measure on `E`
along the extended chart `extChartAt I (d.center i)`.

We define this as a pushforward of the **restricted** measure
`μ.restrict (extChartAt I (d.center i)).source`
so that the value of `extChartAt` outside its source is irrelevant.
-/

/-- The pushforward of a measure `μ` on `M` along the extended chart `extChartAt`. -/
noncomputable def chartMeasure (μ : Measure M) (i : d.ι) : Measure E :=
  (μ.restrict (extChartAt I (d.center i)).source).map (extChartAt I (d.center i))

section

omit [FiniteDimensional ℝ E]

/-- The extended chart is a.e.-measurable with respect to the restricted measure on its source.
@isnad1 id=aemeasur.0h7v.s7.0ed6f8a30ddd from=translated src=- shape=3c689b19 vocab=c5a0a95a
-/
lemma aemeasurable_extChartAt (μ : Measure M) (i : d.ι) :
    AEMeasurable (extChartAt I (d.center i))
      (μ.restrict (extChartAt I (d.center i)).source) := by
  classical
  have hs :
      MeasurableSet (extChartAt I (d.center i)).source :=
    (isOpen_extChartAt_source (I := I) (x := d.center i)).measurableSet
  have hcont :
      Continuous ((extChartAt I (d.center i)).source.domRestrict (extChartAt I (d.center i))) :=
    (continuousOn_iff_continuous_domRestrict).1 (continuousOn_extChartAt (I := I) (x := d.center i))
  exact aemeasurable_restrict_of_measurable_subtype (μ := μ) hs hcont.measurable

end

/--
@isnad1 id=isfinite.0h7v.s6.7bf78e33430f from=translated src=- shape=1b52d252 vocab=1dd508fa
-/
instance instIsFiniteMeasurechartMeasure (μ : Measure M) (i : d.ι) [IsFiniteMeasure μ] :
    IsFiniteMeasure (chartMeasure (d := d) (I := I) μ i) := by
  classical
  delta chartMeasure
  infer_instance

/--
@isnad1 id=isfinite.0h7v.s6.ba9052cfd5cf from=translated src=- shape=139c31e5 vocab=e6201c4e
-/
instance instIsFiniteMeasureOnCompactschartMeasure (μ : Measure M) (i : d.ι) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts (chartMeasure (d := d) (I := I) μ i) := by
  classical
  exact isFiniteMeasureOnCompacts_of_isFiniteMeasure (μ := chartMeasure (d := d) (I := I) μ i)

end FiniteChartData

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
