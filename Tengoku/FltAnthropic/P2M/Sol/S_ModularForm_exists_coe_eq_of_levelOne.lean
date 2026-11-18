import Tengoku
import Tengoku.Seed.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
import Tengoku.Seed.RingTheory.LaurentSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_coe_eq_of_levelOne.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_coe_eq_of_levelOne

open UpperHalfPlane
open scoped MatrixGroups

theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  have hle : ((Γ : Subgroup (GL (Fin 2) ℝ))) ≤ 𝒮ℒ := by
    rintro _ ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  refine ⟨{ toFun := F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, rfl⟩

