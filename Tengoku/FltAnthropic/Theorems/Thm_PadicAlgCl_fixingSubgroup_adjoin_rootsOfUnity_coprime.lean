import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

/--
@isnad1 id=eq.0h1v.s8.4fd7e1778e54 from=translated src=- shape=d03450b5 vocab=227c0e3a
-/
theorem PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime (p : ℕ) [Fact p.Prime] :
    (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}).fixingSubgroup
      = (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by exact @_root_.P2MW.S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime.solution p _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
