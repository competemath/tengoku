import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false

theorem Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
    {A : Type*} [CommRing A] (F : Polynomial (Polynomial A)) (w₀ : A)
    (h0 : (F.eval (Polynomial.C w₀)).coeff 0 = 0)
    (hder : IsUnit ((F.derivative.eval (Polynomial.C w₀)).coeff 0)) (m : ℕ) :
    ∃ w : Fin (m + 1) → A, w 0 = w₀ ∧
      ∀ r : Fin (m + 1), (F.eval (∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w r'))).coeff r = 0 := by exact @_root_.P2MW.S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative.solution A _ F w₀ h0 hder m
