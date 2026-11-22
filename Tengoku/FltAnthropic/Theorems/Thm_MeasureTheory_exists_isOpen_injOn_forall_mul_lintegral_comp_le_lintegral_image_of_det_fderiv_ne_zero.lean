import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

/--
@isnad1 id=ex.2h4v.s8.b8e2df677623 from=translated src=- shape=9c16d223 vocab=2e1a243b
-/
theorem MeasureTheory.exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (a : E) (hf : ContDiffAt ℝ 1 f a) (hf' : (fderiv ℝ f a).det ≠ 0) :
    ∃ s : Set E, IsOpen s ∧ a ∈ s ∧ Set.InjOn f s ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t ⊆ s, MeasurableSet t → ∀ g : E → ℝ≥0∞,
        (δ : ℝ≥0∞) * ∫⁻ x in t, g (f x) ∂μ ≤ ∫⁻ y in f '' t, g y ∂μ := by exact @_root_.P2MW.S_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero.solution E _ _ _ _ _ μ _ f a hf hf'
