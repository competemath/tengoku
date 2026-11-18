import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SL2Elementary
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_closure_elemSet_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_closure_elemSet_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h1v.s7.0cf025ab54f4 from=translated src=- shape=2cf782c4 vocab=96777411
-/
theorem ModularCurve.closure_elemSet_eq_top (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤ := by exact @_root_.P2MW.S_ModularCurve_closure_elemSet_eq_top.solution N _
