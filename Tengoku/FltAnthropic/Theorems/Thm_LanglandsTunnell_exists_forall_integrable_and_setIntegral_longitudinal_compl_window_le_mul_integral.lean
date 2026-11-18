import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.MeasureTheory hiding setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap open _root_.Set

theorem LanglandsTunnell.exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral
    (a : ℝ) (ha : a ≠ 0) (α β : ℝ) (η δ₁ : ℝ) (hη : 0 < η) (hδ₁ : 0 < δ₁) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      Integrable (fun u : ℝ =>
        Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
            + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
          * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ))) ∧
      ∫ u in {u : ℝ | δ₁ < |u - (1 / 3) * Real.log (y / (Real.pi * |a|))|},
          Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
              + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
            * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ))
        ≤ η * ∫ u : ℝ,
          Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
              + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
            * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ)) := by exact @_root_.P2MW.S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral.solution a ha α β η δ₁ hη hδ₁
