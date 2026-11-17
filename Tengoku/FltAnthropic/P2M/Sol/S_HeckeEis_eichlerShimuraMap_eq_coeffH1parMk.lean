import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binaryFormRepSL IsParabolicCocycle coeffH1parMk coeffH1parMk_eq_zero_iff IsEquivariantPrimitiveWith IsEichlerIntegral eichlerShimuraMap eichlerShimuraMap_def IsEichlerIntegral.exists_sub_eq_const IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

/--
@isnad1 id=eq.3h4v.s17.72a0087106aa from=translated src=- shape=addaf67e vocab=11e6bdc4
-/
theorem SolMain.eqmk (n N : ℕ) (f : ℍ → ℂ) {F : ℍ → ↥(BinaryForm ℂ n)}
    (hEI : IsEichlerIntegral n f F)
    (hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F)
    (hpar : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    eichlerShimuraMap n N f
      = coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ := by
  obtain ⟨F₀, hEI₀, h₀, hpar₀, heq⟩ := eichlerShimuraMap_def n N f hEI hF hpar
  rw [heq, ← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]
  obtain ⟨v, hv⟩ := hEI₀.exists_sub_eq_const hEI
  exact h₀.cocycle_sub_cocycle_mem_coeffCoboundaries hF hv

end HeckeEis

end

open scoped MatrixGroups ModularForm in
/--
@isnad1 id=eq.3h4v.s17.72a0087106aa from=translated src=- shape=addaf67e vocab=11e6bdc4
-/
theorem solution (n N : ℕ) (f : UpperHalfPlane → ℂ)
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    HeckeEis.eichlerShimuraMap n N f
      = HeckeEis.coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ :=
  HeckeEis.SolMain.eqmk n N f hEI hF hpar

