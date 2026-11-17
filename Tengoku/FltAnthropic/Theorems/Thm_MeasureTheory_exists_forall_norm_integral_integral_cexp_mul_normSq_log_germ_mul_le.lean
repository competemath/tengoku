import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=ex.1h1v.s9.6798f9e46202 from=translated src=- shape=0d04d1af vocab=fcf2287e
-/
theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ p : ℝ × ℝ, R < |p.1| → h p = 0) →
        (∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) →
      ∀ M : ℝ, (∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
              ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
              h (x, θ)‖ ≤
          K * M * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := by exact @_root_.P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le.solution R hR
