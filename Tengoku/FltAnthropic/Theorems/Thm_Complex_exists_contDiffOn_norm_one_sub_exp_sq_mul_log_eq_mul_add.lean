import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.0h0v.s10.638315238fb6 from=translated src=- shape=19f2eb1b vocab=05eadb92
-/
theorem Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add :
    ∃ a b : ℝ × ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) a {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) b {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → 0 < a p) ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 →
        ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ =
          a p * ((p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) *
              Real.log (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2)) +
            (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) * b p) ∧
      (∀ p : ℝ × ℝ,
        Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) = 1 ↔
          p.1 = 0 ∧ ∃ k : ℤ, p.2 = k) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ =>
          ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖)
        {p : ℝ × ℝ | Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) ≠ 1} := by exact @_root_.P2MW.S_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add.solution
