module

public import Tengoku

public section

open scoped ENNReal
open Filter

namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace β]

variable {mα : MeasurableSpace α} {s : Set α}

/--
@isnad1 id=measurab.1h3v.s5.bd36f3e5b86b from=translated src=- shape=eb09fbe3 vocab=5020f99b
-/
lemma measurable_restrict (hs : MeasurableSet s) : Measurable fun μ : Measure α ↦ μ.restrict s :=
  measurable_of_measurable_coe _ fun t ht ↦ by
    simp_rw [restrict_apply ht]; exact measurable_coe (ht.inter hs)

/--
@isnad1 id=measurab.2h4v.s5.0adf31d240a2 from=translated src=- shape=3de35883 vocab=88ee3065
-/
lemma measurable_setLIntegral {f : α → ℝ≥0∞} (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable fun μ : Measure α ↦ ∫⁻ x in s, f x ∂μ :=
  (measurable_lintegral hf).comp (measurable_restrict hs)

/--
@isnad1 id=iff.2h6v.s6.ec6c559be8cb from=translated src=- shape=4a05c858 vocab=c4b8a726
-/
lemma bind_null {m : Measure α} {f : α → Measure β} {s : Set β}
    (hs : MeasurableSet s) (hf : AEMeasurable f m) :
    m.bind f s = 0 ↔ (fun a ↦ f a s) =ᵐ[m] 0 := by
  rw [bind_apply hs hf]
  exact lintegral_eq_zero_iff' (f := fun a ↦ f a s) <|
    (measurable_coe hs).comp_aemeasurable hf

/--
@isnad1 id=iff.2h6v.s6.57cad01b869e from=translated src=- shape=bd3bbd69 vocab=87ba7af6
-/
theorem ae_bind_iff {m : Measure α} {f : α → Measure β} {p : β → Prop}
    (hf : AEMeasurable f m) (hp : MeasurableSet {x | p x}) :
    (∀ᵐ b ∂m.bind f, p b) ↔ ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b :=
  ⟨ae_ae_of_ae_bind hf, fun h ↦ by
    rwa [ae_iff, bind_null _ hf] at *
    exact hp.compl⟩

end MeasureTheory.Measure
