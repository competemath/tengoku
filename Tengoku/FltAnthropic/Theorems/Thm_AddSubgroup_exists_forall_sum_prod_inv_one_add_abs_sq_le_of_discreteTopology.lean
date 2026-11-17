import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem AddSubgroup.exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology
    {r : ℕ} (Γ : AddSubgroup (Fin r → ℝ)) [DiscreteTopology Γ] :
    ∃ K : ℝ, ∀ (y : Fin r → ℝ) (F : Finset (Fin r → ℝ)), (↑F : Set (Fin r → ℝ)) ⊆ Γ →
      ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ K := by exact @_root_.P2MW.S_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology.solution r Γ _
