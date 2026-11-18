import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_ContinuousUnramified
import Tengoku.FltAnthropic.P2M.Sol.S_IntermediateField_IsUnramifiedOutside_normalClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IntermediateField_IsUnramifiedOutside_normalClosure.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
/--
@isnad1 id=isunrami.1h2v.s8.4ae91bb814a4 from=translated src=- shape=ef26fe78 vocab=0c9ee451
-/
theorem IntermediateField.IsUnramifiedOutside.normalClosure
    {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) :
    (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by exact @_root_.P2MW.S_IntermediateField_IsUnramifiedOutside_normalClosure.solution S F hF
