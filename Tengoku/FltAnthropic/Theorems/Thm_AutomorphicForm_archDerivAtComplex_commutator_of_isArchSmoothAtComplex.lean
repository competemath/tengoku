import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archDerivAtComplex hw .H (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) =
      (-1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ) - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) =
      0 ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) =
      0 ∧
    archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) =
      0 := by exact @_root_.P2MW.S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.solution F _ _ w hw φ hφ
