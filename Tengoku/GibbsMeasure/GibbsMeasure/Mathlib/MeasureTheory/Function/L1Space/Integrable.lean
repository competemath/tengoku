module

public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Measure.AEMeasurable
public import Tengoku

public section

open EMetric ENNReal Filter MeasureTheory NNReal TopologicalSpace Set

variable {α β 𝕜 : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
variable [NormedField 𝕜] {f φ : α → 𝕜}

namespace MeasureTheory

/--
@isnad1 id=integrab.2h6v.s7.99e4a5eb4fae from=translated src=- shape=6085553b vocab=5ebcea5a
-/
@[simp] lemma Integrable.fun_mul_of_top_right (hf : Integrable f μ) (hφ : MemLp φ ∞ μ) :
    Integrable (fun x ↦ φ x * f x) μ := hf.smul_of_top_right hφ

/--
@isnad1 id=integrab.2h6v.s7.a5c4cf3125a2 from=translated src=- shape=57c0477d vocab=5ebcea5a
-/
@[local simp] lemma Integrable.fun_mul_of_top_left (hφ : Integrable φ μ) (hf : MemLp f ∞ μ) :
    Integrable (fun x ↦ φ x * f x) μ :=
  hφ.smul_of_top_left hf

/--
@isnad1 id=measurab.1h6v.s5.ed48d620ced7 from=translated src=- shape=5ab73062 vocab=dc3bb556
-/
@[fun_prop]
lemma Integrable.measurable [TopologicalSpace β] [PseudoMetrizableSpace β] [ContinuousENorm β]
    [μ.IsComplete] {f : α → β} [BorelSpace β] (hf : Integrable f μ) : Measurable f :=
  hf.aemeasurable.measurable

end MeasureTheory
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
