import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_exists_isEichlerIntegral
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

/--
@isnad1 id=ex.0h3v.s14.e746571776c6 from=translated src=- shape=bbe84c03 vocab=debc53a9
-/
theorem solution (N n : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F ∧
      ∃ hF : HeckeEis.IsEquivariantPrimitiveWith
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F,
        HeckeEis.IsParabolicCocycle
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle := by
  obtain ⟨F, hEI⟩ := HeckeEis.exists_isEichlerIntegral n (f := (f : UpperHalfPlane → ℂ)) (CuspFormClass.holo f)
  have hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F :=
    HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral hEI
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ))
  exact ⟨F, hEI, hF, HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral N n f hEI hF⟩
