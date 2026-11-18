import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
    (e : ℤ → ℂ) {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun m : ℤ => ‖e m‖ * r₁ ^ m) (hs₂ : Summable fun m : ℤ => ‖e m‖ * r₂ ^ m)
    (hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → ∑' m : ℤ, e m * z ^ m = 0) : e = 0 := by exact @_root_.P2MW.S_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero.solution e r₁ r₂ h0 h12 hs₁ hs₂ hz
