import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open _root_.MvPowerSeries hiding exists_algEquiv_apply_X_eq span_singleton_isPrime_of_sub_linear_mem_sq exists_eq_X_sub_subst_mul_of_subst_eq_zero

/--
@isnad1 id=ex.3h7v.s11.58551bc68035 from=translated src=- shape=aef8e6fa vocab=ee569edb
-/
theorem MvPowerSeries.exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero
    {κ : Type u} [Field κ] {ι : Type v} [Fintype ι]
    (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (A B : ι → κ) (hsimple : ∀ i, a * B i - A i * b ≠ 0)
    (f : MvPowerSeries (Fin 2) κ)
    (hf : f - (C a * X 0 + C b * X 1) * ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 2)) :
    ∃ (L f₁ : MvPowerSeries (Fin 2) κ),
      L - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 ∧
      f₁ - ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1) ∧
      f = L * f₁ := by exact @_root_.P2MW.S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero.solution κ _ ι _ a b hab A B hsimple f hf
