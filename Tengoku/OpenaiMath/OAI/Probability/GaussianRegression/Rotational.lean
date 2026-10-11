import Tengoku.OpenaiMath.OAI.Probability.GaussianRegression.Sphere

namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

lemma prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod_symm _ hm]
  apply (lintegral_mono_ae ?_).trans_eq (lintegral_const c)
  filter_upwards [h, ae_fiber_aemeasurable hm] with y hy hmy
  have hs : NullMeasurableSet {x | (x,y) ∈ S} μ := by
    have heq : {x | (x,y) ∈ S} = {x | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext x
      by_cases hx : (x,y) ∈ S <;> simp [hx]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmy aemeasurable_const
  change (∫⁻ x, ({x | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) ≤ c
  simpa [lintegral_indicator_const₀ hs] using hy
end FubiniAux

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

namespace Learner
lemma run_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) (n : ℕ) :
    L.run s ω x n = L.run t ω x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    split
    · rfl
    · split
      · rw [h]
      · rfl

lemma estimate_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) : L.estimate s ω x = L.estimate t ω x := by
  simp only [estimate, terminal, run_congr_labels L s t ω x h]

lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

end Learner

end NoiselessRegression

end

end OAI
