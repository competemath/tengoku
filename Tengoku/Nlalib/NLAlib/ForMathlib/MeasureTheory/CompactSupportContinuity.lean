import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.MeasureTheory.Measure.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Parametric continuity on a compact support fibre

Joint continuity is needed only on the compact parameter set times the
actual compact support of a finite measure. Uniform domination and all
measurability follow there, without conditions elsewhere.
-/

noncomputable section
open MeasureTheory Set
namespace MeasureTheory

/-- A jointly continuous compactly supported fibre integral depends
continuously on a compact parameter set. No regularity of the integrand
outside the actual support is required.
@isnad1 id=continuo.3h6v.s7.bd993e7c3144 from=translated src=- shape=2f2eccb5 vocab=f8b29b43
-/
theorem continuousOn_integral_of_continuousOn_compact_support
    {X Ω E : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {K : Set X} (hK : IsCompact K) {F : X → Ω → E}
    (hF : ContinuousOn (Function.uncurry F) (K ×ˢ μ.support)) :
    ContinuousOn (fun x => ∫ y, F x y ∂μ) K := by
  obtain ⟨C, hC⟩ := (hK.prod hμ).bddAbove_image hF.norm
  have hre : μ.restrict μ.support = μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro x hx
    have hs : ContinuousOn (F x) μ.support :=
      hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hx, hy⟩)
    have hm := hs.aestronglyMeasurable_of_isCompact (μ := μ) hμ hμ.measurableSet
    rwa [hre] at hm
  · intro x hx
    filter_upwards [μ.support_mem_ae] with y hy
    exact hC ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards [μ.support_mem_ae] with y hy
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, hy⟩)

end MeasureTheory
