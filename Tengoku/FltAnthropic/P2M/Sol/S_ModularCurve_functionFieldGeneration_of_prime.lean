import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_functionFieldGeneration_of_prime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_functionFieldGeneration_of_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ :=by
  intro d hd hne
  haveI := hne
  rcases (Nat.dvd_prime hℓ).mp hd with rfl | rfl
  · rw [qExpand_one_apply]
    exact subset_adjoin ℚ _ (Set.mem_insert _ _)
  · exact subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

end
