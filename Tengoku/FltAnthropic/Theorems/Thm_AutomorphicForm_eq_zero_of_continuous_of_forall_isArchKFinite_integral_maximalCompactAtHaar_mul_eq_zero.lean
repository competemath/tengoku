import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchKFinite
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
    (K : Type) [Field K] [NumberField K]
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_h : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f → IsArchKFinite K f →
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) = 0) :
    β = 0 := by exact @_root_.P2MW.S_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero.solution K _ _ β _hβ _h
