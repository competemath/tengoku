import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
    (N : ℕ) (hN : 3 ≤ N) :
    (∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹) ≠ 0 ∧
    ∃ a : ℕ,
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)) ∧
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)⁻¹) := by exact @_root_.P2MW.S_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral.solution N hN
