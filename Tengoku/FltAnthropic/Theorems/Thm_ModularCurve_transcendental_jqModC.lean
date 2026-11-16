import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_transcendental_jqModC

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_transcendental_jqModC.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve
/--
@isnad1 id=transcen.0h1v.s6.c6b1ea012d94 from=translated src=- shape=a638af76 vocab=2c21e622
-/
theorem ModularCurve.transcendental_jqModC (K : Type*) [CommRing K] :
    Transcendental K (jqModC K) := by exact @_root_.P2MW.S_ModularCurve_transcendental_jqModC.solution K _
