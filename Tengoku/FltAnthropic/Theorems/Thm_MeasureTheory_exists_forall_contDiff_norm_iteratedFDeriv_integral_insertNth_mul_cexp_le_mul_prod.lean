import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
    (n N : ℕ) (k : Fin (n + 1)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : (Fin (n + 1) → ℝ) × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ i, R < |p.1 i|) → g p = 0) →
      ∀ M : ℝ, (∀ i : ℕ, i ≤ N + 2 * n → ∀ p : (Fin (n + 1) → ℝ) × ℝ, ‖iteratedFDeriv ℝ i g p‖ ≤ M) →
      ∀ ξ' : Fin n → ℝ,
        let h : ℝ × ℝ → ℂ := fun q =>
          ∫ x' : Fin n → ℝ, g (Fin.insertNth k q.1 x', q.2) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ)))
        ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧
          ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
            ‖iteratedFDeriv ℝ i h q‖ ≤ K * M * ∏ i', (1 + |ξ' i'|)⁻¹ ^ 2 := by exact @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod.solution n N k R hR
