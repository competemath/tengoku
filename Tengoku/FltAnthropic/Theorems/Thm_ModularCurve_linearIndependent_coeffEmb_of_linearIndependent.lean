import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ModularCurve

universe u v

theorem ModularCurve.linearIndependent_coeffEmb_of_linearIndependent
    (L : Type u) [Field L] [CharZero L]
    {ι : Type v} {v : ι → LaurentSeries ℚ} (hv : LinearIndependent ℚ v) :
    LinearIndependent L (fun i => coeffEmb L (v i)) := by exact @_root_.P2MW.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent.solution L _ _ ι v hv
