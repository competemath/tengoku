import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_CoordRing
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_isDomain_coordRing_of_ne_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem DrinfeldCurve.isDomain_coordRing_of_ne_one (q : ℕ) (hq : q ≠ 1) (k : Type u) [Field k] :
    IsDomain (DrinfeldCurve.CoordRing q k) := by exact @_root_.P2MW.S_DrinfeldCurve_isDomain_coordRing_of_ne_one.solution q hq k _
