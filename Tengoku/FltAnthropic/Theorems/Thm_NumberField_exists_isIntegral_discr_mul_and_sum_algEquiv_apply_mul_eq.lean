import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem NumberField.exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ j, IsIntegral ℤ (a j)) ∧ (∀ j, IsIntegral ℤ ((NumberField.discr K : K) * b j)) ∧
      (∀ γ : K ≃ₐ[ℚ] K, ∑ j, γ (a j) * γ (b j) = 1) ∧
      ∀ γ δ : K ≃ₐ[ℚ] K, γ ≠ δ → ∑ j, γ (a j) * δ (b j) = 0 := by exact @_root_.P2MW.S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq.solution K _ _ _
