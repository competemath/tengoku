import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_ModuliPoint_mk_eq_mk_iff_step.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ModularCurve.ModuliPoint.mk_eq_mk_iff_step
    {N : ℕ} {L : Type*} [Field L] [DecidableEq L] (P Q : ModularCurve.Gamma0Pair N L) :
    (Quot.mk _ P : ModularCurve.ModuliPoint N L) = Quot.mk _ Q ↔ ModularCurve.Gamma0Pair.Step P Q := by exact @_root_.P2MW.S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step.solution N L _ _ P Q
