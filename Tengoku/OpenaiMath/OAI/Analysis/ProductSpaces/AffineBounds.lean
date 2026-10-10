import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.CoefficientLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uO uR uS uΛ uΩ uι

namespace IndependentProducts
section MeasureDiagram
variable {S : Type uS} {R : Type uR} {O : Type uO}
  [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace O]
variable {Ps : Measure S} {Pr : Measure R} {Po : Measure O} {q : S → R} {s : S → O}

lemma integral_measure_diagram (hq : MeasurePreserving q Ps Pr) (hs : MeasurePreserving s Ps Po)
    (f : R → ℝ) (g : O → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, f (q z) = g (s z)) : ∫ z, f z ∂Pr = ∫ ω, g ω ∂Po := by
  rw [← hq.hasLaw.integral_comp hf.aestronglyMeasurable,
    ← hs.hasLaw.integral_comp hg.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ he)

lemma integrable_measure_diagram (hq : MeasurePreserving q Ps Pr) (hs : MeasurePreserving s Ps Po)
    (f : R → ℝ) (g : O → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, f (q z) = g (s z)) (hi : Integrable g Po) : Integrable f Pr := by
  apply (hq.integrable_comp hf.aestronglyMeasurable).mp
  apply Integrable.congr ((hs.integrable_comp hg.aestronglyMeasurable).mpr hi)
  exact Filter.EventuallyEq.symm (ae_of_all Ps he)

end MeasureDiagram

lemma measurable_joint_firstExitSum {Λ : Type uΛ} {Ω : Type uΩ} {ι : Type uι}
    [MeasurableSpace Λ] [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (B : Λ → ι → Ω → ℝ)
    (hB : ∀ i, Measurable (fun z : Λ × Ω => B z.1 i z.2))
    (hm : ∀ i, Measurable (fun l => ∫ b, B l i b ∂ν)) :
    Measurable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1) := by
  unfold firstExitSum
  apply Finset.measurable_sum
  intro i hi
  exact (((hB i).comp
    (measurable_snd.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)))).mul
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))).sub
        ((hm i).comp measurable_snd)

namespace FiniteHead
section FiniteAffine
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (hmean : ∫ w : ℝ, w ∂μ = 1)
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)
variable (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (hv : ∀ k, (e (j k)).val.val <+: v k)

lemma measurable_tailCoefficient_section (old : Sample) (i : ι) :
    Measurable (T.tailCoefficient e v j a old i) :=
  Measurable.of_uncurry_left (f := fun old desc => T.tailCoefficient e v j a old i desc)
    (T.measurable_tailCoefficient e v j a i)

end FiniteAffine
end FiniteHead
end IndependentProducts

end

end OAI
