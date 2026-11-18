import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LegendreJ

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_legendreJ_eq_zero_iff.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_legendreJ_eq_zero_iff

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (legendreJ)
open _root_.ModularCurve

theorem legendreJ_eq_zero_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  rw [legendreJ, div_eq_zero_iff, or_iff_left hden, mul_eq_zero, or_iff_right (pow_ne_zero _ h2)]
  exact pow_eq_zero_iff three_ne_zero

end ModularCurve

open _root_.ModularCurve open _root_.P2MW.S_ModularCurve_legendreJ_eq_zero_iff.ModularCurve

theorem solution {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 :=
  ModularCurve.legendreJ_eq_zero_iff' h2 ht0 ht1
