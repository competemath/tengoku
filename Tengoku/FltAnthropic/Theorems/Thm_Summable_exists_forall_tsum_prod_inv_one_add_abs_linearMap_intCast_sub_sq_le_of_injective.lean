import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Summable.exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective
    (a r : ℕ) (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hA : Function.Injective A) :
    ∃ K : ℝ, ∀ t : Fin r → ℝ,
      Summable (fun k : Fin a → ℤ => ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2) ∧
      ∑' k : Fin a → ℤ, ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2 ≤ K := by exact @_root_.P2MW.S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective.solution a r A hA
