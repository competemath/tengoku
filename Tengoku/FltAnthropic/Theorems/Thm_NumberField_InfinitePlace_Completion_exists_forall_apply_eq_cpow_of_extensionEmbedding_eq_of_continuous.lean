import Tengoku.Seed.NumberTheory.NumberField.Completion.InfinitePlace
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

/--
@isnad1 id=ex.1h3v.s10.3c40992901f9 from=translated src=- shape=fbb2da1a vocab=38946801
-/
theorem NumberField.InfinitePlace.Completion.exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous
    (F : Type) [Field F] (w : InfinitePlace F)
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχc : Continuous fun x : (w.Completion)ˣ => ((χ x : ℂˣ) : ℂ)) :
    ∃ s : ℂ,
      (∀ (u : (w.Completion)ˣ) (r : ℝ), 0 < r → extensionEmbedding w (u : w.Completion) = (r : ℂ) →
        ((χ u : ℂˣ) : ℂ) = (r : ℂ) ^ s) ∧
      ((∀ u : (w.Completion)ˣ, ‖((χ u : ℂˣ) : ℂ)‖ = 1) → s.re = 0) := by exact @_root_.P2MW.S_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous.solution F _ w χ _hχc
