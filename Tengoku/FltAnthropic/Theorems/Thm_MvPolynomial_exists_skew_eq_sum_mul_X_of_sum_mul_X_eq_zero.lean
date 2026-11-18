import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

theorem MvPolynomial.exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero
    (B : Type*) [CommRing B] {m : ℕ} (c : Fin m → MvPolynomial (Fin m) B)
    (hc : ∑ j, c j * MvPolynomial.X j = 0) :
    ∃ e : Fin m → Fin m → MvPolynomial (Fin m) B,
      (∀ j k, e j k = -e k j) ∧ (∀ j, e j j = 0) ∧ ∀ j, c j = ∑ k, e j k * MvPolynomial.X k := by exact @_root_.P2MW.S_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero.solution B _ m c hc
