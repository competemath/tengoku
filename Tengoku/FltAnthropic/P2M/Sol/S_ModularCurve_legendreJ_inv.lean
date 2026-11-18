import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LegendreJ

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_legendreJ_inv.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_legendreJ_inv

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (legendreJ)
open _root_.ModularCurve

/--
@isnad1 id=eq.0h2v.s5.6b669a21eca1 from=translated src=- shape=e841f6b3 vocab=7d41956a
-/
theorem legendreJ_inv' {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [inv_zero]
  have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have hu : (t⁻¹ : K) ≠ 0 := inv_ne_zero ht
  have e1 : (t⁻¹ ^ 2 - t⁻¹ + 1) ^ 3 = (t ^ 2 - t + 1) ^ 3 * t⁻¹ ^ 6 := by
    linear_combination (-t^5*t⁻¹^5 + 3*t^4*t⁻¹^5 - t^4*t⁻¹^4 - 6*t^3*t⁻¹^5 + 3*t^3*t⁻¹^4 - t^3*t⁻¹^3 + 7*t^2*t⁻¹^5 - 6*t^2*t⁻¹^4 + 3*t^2*t⁻¹^3 - t^2*t⁻¹^2 - 6*t*t⁻¹^5 + 7*t*t⁻¹^4 - 6*t*t⁻¹^3 + 3*t*t⁻¹^2 - t*t⁻¹ + 3*t⁻¹^5 - 6*t⁻¹^4 + 7*t⁻¹^3 - 6*t⁻¹^2 + 3*t⁻¹ - 1) * hi
  have e2 : t⁻¹ ^ 2 * (t⁻¹ - 1) ^ 2 = (t ^ 2 * (t - 1) ^ 2) * t⁻¹ ^ 6 := by
    linear_combination (-t^3*t⁻¹^5 + 2*t^2*t⁻¹^5 - t^2*t⁻¹^4 - t*t⁻¹^5 + 2*t*t⁻¹^4 - t*t⁻¹^3 - t⁻¹^4 + 2*t⁻¹^3 - t⁻¹^2) * hi
  simp only [legendreJ]
  rw [e1, e2, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero 6 hu)]

end ModularCurve

open _root_.ModularCurve open _root_.P2MW.S_ModularCurve_legendreJ_inv.ModularCurve

/--
@isnad1 id=eq.0h2v.s5.6b669a21eca1 from=translated src=- shape=e841f6b3 vocab=7d41956a
-/
theorem solution {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t :=
  ModularCurve.legendreJ_inv' t
