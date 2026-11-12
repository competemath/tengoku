import Tengoku.AbelFormalization.AbelFormalization.LowerDimensionalImageAvoidance
import Tengoku.Seed.MeasureTheory.Function.Jacobian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simultaneous avoidance of countably many critical-value sets

Mathlib's fixed-dimensional Sard lemma makes the image of each specified
critical set Haar-null.  Countable subadditivity and positivity of
finite-dimensional Hausdorff measure then supply a point outside all images.
-/

noncomputable section

open Set Function
open scoped MeasureTheory ENNReal

namespace AbelFormalization

set_option autoImplicit false

/--
@isnad1 id=eq.2h4v.s8.7d6d9b9410ad from=translated src=- shape=c7953351 vocab=d1b1dfae
-/
theorem addHaar_image_criticalSet_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : MeasureTheory.Measure E) [mu.IsAddHaarMeasure]
    {f : E → E} {s : Set E}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hdet : ∀ x ∈ s, (fderiv ℝ f x).det = 0) :
    mu (f '' s) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (f' := fun x ↦ fderiv ℝ f x)
  · intro x hx
    exact (hf x hx).hasFDerivAt.hasFDerivWithinAt
  · exact hdet

/--
@isnad1 id=ex.2h4v.s7.a3cde431983f from=translated src=- shape=657ec95f vocab=07308e54
-/
theorem exists_avoiding_countable_critical_images
    {ι E : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : ι → E → E) (s : ι → Set E)
    (hf : ∀ i, ∀ x ∈ s i, DifferentiableAt ℝ (f i) x)
    (hdet : ∀ i, ∀ x ∈ s i, (fderiv ℝ (f i) x).det = 0) :
    ∃ c : E, ∀ i, c ∉ f i '' s i := by
  let bad : Set E := ⋃ i, f i '' s i
  have hbad : μH[Module.finrank ℝ E] bad = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro i
    exact addHaar_image_criticalSet_eq_zero
      (μH[Module.finrank ℝ E] : MeasureTheory.Measure E)
      (hf i) (hdet i)
  have hbadne : bad ≠ Set.univ := by
    intro hbaduniv
    have hunivzero : μH[Module.finrank ℝ E] (Set.univ : Set E) = 0 := by
      simpa [hbaduniv] using hbad
    exact (isOpen_univ.measure_ne_zero
      (μH[Module.finrank ℝ E] : MeasureTheory.Measure E) univ_nonempty)
      hunivzero
  obtain ⟨c, hc⟩ := Set.nonempty_compl.mpr hbadne
  refine ⟨c, fun i hci ↦ ?_⟩
  exact hc (Set.mem_iUnion.2 ⟨i, hci⟩)

end AbelFormalization
