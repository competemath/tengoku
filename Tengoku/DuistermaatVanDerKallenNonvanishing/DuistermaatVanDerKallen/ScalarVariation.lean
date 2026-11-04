import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.RegularJacobian
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CountableSemialgebraic
import Tengoku.Seed.Topology.Algebra.Module.Determinant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform variation bounds for locally C¹ scalar semialgebraic families.
The source fibers are real line fibers, so no projection or Hardt input is
needed. Actual derivatives and measurable source sets are supplied. Finite exceptional
sets may vary arbitrarily with the parameters; no uniform bound on their
cardinality or semialgebraicity of their total family is required. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

/-- Deleting finitely many nonsmooth source points needs no semialgebraicity
or uniform cardinal bound for the exceptional sets. The full graph supplies
the uniform multiplicity constant.
@isnad1 id=ex.5h6v.s8.71452c6f687c from=translated src=- shape=fb9558b8 vocab=9c38ccaf
-/
theorem uniform_semialgebraic_scalar_variation_off_finite
    {ι : Type*} (μ : Measure ℝ) [IsAddHaarMeasure μ]
    (S T : (ι → ℝ) → Set ℝ) (hS : ∀ a, MeasurableSet (S a))
    (hT : ∀ a, (T a).Finite)
    (f d : (ι → ℝ) → ℝ → ℝ)
    (hgraph : IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ S (fun j => q (.inl (.inl j))) ∧
      f (fun j => q (.inl (.inl j))) (q (.inr ())) = q (.inl (.inr ()))})
    (hf : ∀ a, ∀ x ∈ S a, x ∉ T a → ContDiffAt ℝ 1 (f a) x)
    (hd : ∀ a, ∀ x ∈ S a, x ∉ T a → HasDerivAt (f a) (d a x) x) :
    ∃ N : ℕ, ∀ a, (∫⁻ x in S a \ T a, ENNReal.ofReal |d a x| ∂μ) ≤
      (N : ℝ≥0∞) * μ (f a '' (S a \ T a)) := by
  obtain ⟨N, hN⟩ := hgraph.uniform_finite_line_fibers
  refine ⟨N, fun a => ?_⟩
  let E := S a \ T a
  have hE : MeasurableSet E := (hS a).diff (hT a).isClosed.measurableSet
  let D (x : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (d a x)
  have hD (x : ℝ) (hx : x ∈ E) : HasFDerivAt (f a) (D x) x := hd a x hx.1 hx.2
  have hC (x : ℝ) (hx : x ∈ E) : ContDiffAt ℝ 1 (f a) x := hf a x hx.1 hx.2
  have hc := ae_countable_fibers_of_contDiffAt μ E (f a) D hC hD
  have hb := lintegral_abs_det_le_mul_image_of_contDiffAt μ E hE (f a) D hC hD N (by
    filter_upwards [hc] with y hy
    have hfull : ({x | x ∈ S a ∧ f a x = y}).Countable := by
      apply (hy.union (hT a).countable).mono
      intro x hx
      by_cases hxT : x ∈ T a
      · exact Or.inr hxT
      · exact Or.inl ⟨⟨hx.1, hxT⟩, hx.2⟩
    have hfinite : ({x | x ∈ S a ∧ f a x = y}).Finite :=
      hgraph.finite_line_fiber_of_countable (Sum.elim a (fun _ => y)) hfull
    have hsub : {x | x ∈ E ∧ f a x = y} ⊆ {x | x ∈ S a ∧ f a x = y} :=
      fun x hx => ⟨hx.1.1, hx.2⟩
    exact ⟨hfinite.subset hsub, (Set.ncard_le_ncard hsub hfinite).trans
      (hN (Sum.elim a (fun _ => y)) hfinite)⟩)
  simpa only [D, ContinuousLinearMap.det_toSpanSingleton] using hb

/-- The no-exception specialization.
@isnad1 id=ex.4h5v.s8.ff5c95f5eb95 from=translated src=- shape=92451a78 vocab=911b3ff4
-/
theorem uniform_semialgebraic_scalar_variation
    {ι : Type*} (μ : Measure ℝ) [IsAddHaarMeasure μ]
    (E : (ι → ℝ) → Set ℝ) (hE : ∀ a, MeasurableSet (E a))
    (f d : (ι → ℝ) → ℝ → ℝ)
    (hgraph : IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ E (fun j => q (.inl (.inl j))) ∧
      f (fun j => q (.inl (.inl j))) (q (.inr ())) = q (.inl (.inr ()))})
    (hf : ∀ a, ∀ x ∈ E a, ContDiffAt ℝ 1 (f a) x)
    (hd : ∀ a, ∀ x ∈ E a, HasDerivAt (f a) (d a x) x) :
    ∃ N : ℕ, ∀ a, (∫⁻ x in E a, ENNReal.ofReal |d a x| ∂μ) ≤
      (N : ℝ≥0∞) * μ (f a '' E a) := by
  simpa only [Set.sdiff_empty] using uniform_semialgebraic_scalar_variation_off_finite
    μ E (fun _ => ∅) hE (fun _ => Set.finite_empty) f d hgraph
    (fun a x hx _ => hf a x hx) (fun a x hx _ => hd a x hx)

end
end DuistermaatVanDerKallen
