import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.FltAnthropic.P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Filter Topology Asymptotics
/--
@isnad1 id=isbigo.0h1v.s6.c250cad75475 from=translated src=- shape=938ffee7 vocab=a91a3bd0
-/
theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by exact @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution K _ _
