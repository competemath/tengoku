import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Topology Polynomial

/--
@isnad1 id=ex.2h3v.s9.b225e64faa52 from=translated src=- shape=49604967 vocab=38c51a60
-/
theorem Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
    (F : Polynomial (Polynomial ℂ)) (z₀ w₀ : ℂ)
    (h₀ : F.evalEval z₀ w₀ = 0) (hd : (Polynomial.derivative F).evalEval z₀ w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : ℂ → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ F.evalEval z (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, F.evalEval z w = 0 → w = φ z) := by exact @_root_.P2MW.S_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero.solution F z₀ w₀ h₀ hd
