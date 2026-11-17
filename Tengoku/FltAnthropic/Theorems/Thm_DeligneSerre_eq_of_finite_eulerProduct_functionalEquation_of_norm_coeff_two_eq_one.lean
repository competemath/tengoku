import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℤ) (ω : ℂ) (hω : ω ≠ 0)
    (P Q P' Q' : ℕ → ℂ[X])
    (hP₀ : ∀ p ∈ S, (P p).coeff 0 = 1) (hQ₀ : ∀ p ∈ S, (Q p).coeff 0 = 1)
    (hP'₀ : ∀ p ∈ S, (P' p).coeff 0 = 1) (hQ'₀ : ∀ p ∈ S, (Q' p).coeff 0 = 1)
    (hP : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hP' : ∀ p ∈ S, ∀ z : ℂ, (P' p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hQ : ∀ p ∈ S,
      ((∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∧
          ∀ z : ℂ, (Q' p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1) ∧ (∀ z : ℂ, (P' p).IsRoot z → ‖z‖ = 1) ∧
          (Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1 ∧
          (Q' p).natDegree ≤ 2 ∧ ‖(Q' p).coeff 2‖ = 1))
    (σ₀ : ℝ)
    (hFE : ∀ s : ℝ, σ₀ ≤ s →
      (∏ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p)) *
          ∏ p ∈ S, (P' p).eval ((p : ℂ) ^ ((s : ℂ) - 1)) * (Q p).eval ((p : ℂ) ^ (-(s : ℂ))) =
        ω * ∏ p ∈ S, (P p).eval ((p : ℂ) ^ (-(s : ℂ))) * (Q' p).eval ((p : ℂ) ^ ((s : ℂ) - 1))) :
    ∀ p ∈ S, e p = 0 ∧ P p = Q p ∧ P' p = Q' p := by exact @_root_.P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.solution S hS e ω hω P Q P' Q' hP₀ hQ₀ hP'₀ hQ'₀ hP hP' hQ σ₀ hFE
