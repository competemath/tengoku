import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.2h2v.s9.b2328283d4d4 from=translated src=- shape=91ede20f vocab=bbb2a9ee
-/
theorem Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
        {p : ℝ × ℝ | p ≠ 0} ∧
      ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
        ‖p‖ ^ n *
            ‖iteratedFDeriv ℝ n
                (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
                p‖ ≤
          C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := by exact @_root_.P2MW.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le.solution α β hα hβ
