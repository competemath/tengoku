import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Tengoku.FltAnthropic.P2M.Sol.S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open FLT.SmoothVectors
theorem FLT.SmoothVectors.gl2CongruenceSubgroup_zero_eq_integralSubgroup
    (p : ℕ) [Fact p.Prime] :
    gl2CongruenceSubgroup p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by exact @_root_.P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.solution p _
