import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LegendreJ
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_legendreJ_eq_zero_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_legendreJ_eq_zero_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve
theorem ModularCurve.legendreJ_eq_zero_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by exact @_root_.P2MW.S_ModularCurve_legendreJ_eq_zero_iff.solution K _ h2 t ht0 ht1
