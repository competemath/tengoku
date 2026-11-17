import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.P2M.Sol.S_FreyPackage_padicValInt_two_freyCurveInt_discr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FreyPackage_padicValInt_two_freyCurveInt_discr.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/--
@isnad1 id=eq.0h1v.s6.3ad79a3b3753 from=translated src=- shape=67e522ac vocab=276b7411
-/
theorem Tengoku.FltAnthropic.FreyPackage.padicValInt_two_freyCurveInt_discr (P : FreyPackage) :
    padicValInt 2 P.freyCurveInt.Δ + 8 = 2 * P.p * padicValInt 2 (P.a * P.b * P.c) := by exact @_root_.P2MW.S_FreyPackage_padicValInt_two_freyCurveInt_discr.solution P
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
