import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=ex.1h1v.s9.d82b29883927 from=translated src=- shape=80cfca5a vocab=f9442b53
-/
theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ℝ × ℝ → ℂ), ContDiff ℝ 4 F → (∀ p : ℝ × ℝ, R < |p.1| → F p = 0) →
        (∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) →
      ∀ B : ℝ, (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ B) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) * F (x, θ)‖ ≤
          C * B * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2 := by exact @_root_.P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic.solution R hR
