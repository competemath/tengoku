import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
        ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0} →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ r →
            ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) →
        ContDiff ℝ 4 H → (∀ p : ℝ × ℝ, r ≤ ‖p‖ → H p = 0) →
        (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n H p‖ ≤ B) →
        ∀ ξ η : ℝ,
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ))) *
              ((G p : ℂ) * H p)‖ ≤
            C * A * B * ((1 + |ξ| + |η|) ^ (7 / 2 : ℝ))⁻¹ := by exact @_root_.P2MW.S_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log.solution r hr
