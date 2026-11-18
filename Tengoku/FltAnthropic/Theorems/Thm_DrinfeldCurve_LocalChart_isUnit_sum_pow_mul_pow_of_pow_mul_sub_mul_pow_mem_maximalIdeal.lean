import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W] (hqW : (q : W) ∈ maximalIdeal W)
    (a b : W) (hab : a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W)
    (hdir : a ^ q * b - a * b ^ q ∈ maximalIdeal W) :
    IsUnit (∑ i ∈ Finset.range (q + 1), a ^ ((q - 1) * i) * b ^ ((q - 1) * (q - i))) := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal.solution q _ W _ _ hqW a b hab hdir
