import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WindingDatum
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem AutomorphicForm.WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
    {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ (i : ℕ) (n : Fin d → ℤ),
        Summable (fun γ : 𝒟.sub i => ‖𝒟.fibreTerm i n γ‖) ∧
        ∑' γ : 𝒟.sub i, ‖𝒟.fibreTerm i n γ‖ ≤ K * 𝒟.C i ∧
        ‖𝒟.fibreCoeff i n‖ ≤ K * 𝒟.C i) ∧
      ∀ n : Fin d → ℤ, Summable fun i : ℕ => ‖𝒟.lam i * 𝒟.fibreCoeff i n‖ := by exact @_root_.P2MW.S_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le.solution r d c 𝒟
