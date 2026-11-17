import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
    {r : ℕ} (f : (Fin r → ℝ) → ℂ) (hf : Continuous f) (hfi : Integrable f) (C : ℝ)
    (hC : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x‖ ≤ C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
    (x : Fin r → ℝ) :
    ‖f x‖ ≤ 2 ^ r * C := by exact @_root_.P2MW.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod.solution r f hf hfi C hC x
