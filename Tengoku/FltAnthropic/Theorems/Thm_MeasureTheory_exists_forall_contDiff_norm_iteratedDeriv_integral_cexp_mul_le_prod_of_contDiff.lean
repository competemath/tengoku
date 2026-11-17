import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) h →
        (∀ p : ℝ × (Fin n → ℝ), R < |p.1| → h p = 0) → (∀ p : ℝ × (Fin n → ℝ), (∃ k, R < |p.2 k|) → h p = 0) →
      ∀ M : ℝ, (∀ N : ℕ, N ≤ 2 * n + 2 → ∀ p : ℝ × (Fin n → ℝ), ‖iteratedFDeriv ℝ N h p‖ ≤ M) →
      ∀ ξ : Fin n → ℝ,
        ContDiff ℝ 2 (fun x : ℝ =>
          ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) ∧
        (∀ x : ℝ, R < |x| →
          (∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) = 0) ∧
        ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
          ‖iteratedDeriv j (fun x : ℝ =>
              ∫ y : Fin n → ℝ, h (x, y) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * y k : ℝ) : ℂ)))) x‖ ≤
            K * M * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by exact @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff.solution n R hR
