import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .E φ) - archDerivAt hw .E (archDerivAt hw .H φ) = (2 : ℂ) • archDerivAt hw .E φ ∧
    archDerivAt hw .H (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .H φ) = (-2 : ℂ) • archDerivAt hw .Fm φ ∧
    archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .H φ := by exact @_root_.P2MW.S_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt.solution F _ _ w hw φ hφ
