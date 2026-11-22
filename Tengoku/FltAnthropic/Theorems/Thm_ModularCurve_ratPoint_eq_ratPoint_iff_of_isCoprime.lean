import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CuspSpace
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open OnePoint
/--
@isnad1 id=iff.2h4v.s5.21b1e65e407b from=translated src=- shape=31eb8f55 vocab=ea568b16
-/
theorem ModularCurve.ratPoint_eq_ratPoint_iff_of_isCoprime {a c a' c' : ℤ} (h : IsCoprime a c)
    (h' : IsCoprime a' c') :
    ModularCurve.ratPoint a c = ModularCurve.ratPoint a' c' ↔ (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by exact @_root_.P2MW.S_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.solution a c a' c' h h'
