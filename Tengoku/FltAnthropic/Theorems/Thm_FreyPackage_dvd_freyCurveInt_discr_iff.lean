import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.P2M.Sol.S_FreyPackage_dvd_freyCurveInt_discr_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FreyPackage_dvd_freyCurveInt_discr_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/--
@isnad1 id=iff.1h2v.s5.ef63a4913ce5 from=translated src=- shape=19ed9daf vocab=7120ff69
-/
theorem Tengoku.FltAnthropic.FreyPackage.dvd_freyCurveInt_discr_iff (P : FreyPackage) {q : ℕ} (hq : q.Prime) :
    (q : ℤ) ∣ P.freyCurveInt.Δ ↔ (q : ℤ) ∣ P.a * P.b * P.c := by exact @_root_.P2MW.S_FreyPackage_dvd_freyCurveInt_discr_iff.solution P q hq
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
