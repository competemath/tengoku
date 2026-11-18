import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=eq.1h2v.s7.549b2a84d1af from=translated src=- shape=5cbda88a vocab=a525c03a
-/
theorem MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
    (h : ℝ → ℝ → ℂ) (t : ℝ) (ht : 0 < t) :
    ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), h y₁ y₂ =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((u / (t * v ^ 2) : ℝ) : ℂ) * h (-(u / t)) (u / v) := by exact @_root_.P2MW.S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div.solution h t ht
