import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Topology Polynomial

/--
@isnad1 id=ex.2h4v.s10.a9f55c707c5d from=translated src=- shape=c968c287 vocab=3ff5775b
-/
theorem Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
    {n : ℕ} (F : Polynomial (MvPolynomial (Fin n) ℂ)) (z₀ : Fin n → ℂ) (w₀ : ℂ)
    (h₀ : (F.map (MvPolynomial.eval z₀)).eval w₀ = 0)
    (hd : ((Polynomial.derivative F).map (MvPolynomial.eval z₀)).eval w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : (Fin n → ℂ) → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧ ContDiffOn ℂ ⊤ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ (F.map (MvPolynomial.eval z)).eval (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, (F.map (MvPolynomial.eval z)).eval w = 0 → w = φ z) := by exact @_root_.P2MW.S_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi.solution n F z₀ w₀ h₀ hd
