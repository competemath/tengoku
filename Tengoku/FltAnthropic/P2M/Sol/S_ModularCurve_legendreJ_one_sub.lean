import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LegendreJ

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_legendreJ_one_sub.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_legendreJ_one_sub

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (legendreJ)
open _root_.ModularCurve

end ModularCurve

open _root_.ModularCurve open _root_.P2MW.S_ModularCurve_legendreJ_one_sub.ModularCurve

/--
@isnad1 id=eq.0h2v.s5.a66583b1c258 from=translated src=- shape=0b5d9139 vocab=624010c0
-/
theorem solution {K : Type*} [Field K] (t : K) : legendreJ (1 - t) = legendreJ t := by
  simp only [legendreJ]
  ring
