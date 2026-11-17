import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_IsEichlerIntegral_slash
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binaryFormRepSL IsEquivariantPrimitiveWith IsEichlerIntegral IsEichlerIntegral.slash IsEichlerIntegral.exists_sub_eq_const)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem SolMain.p1b
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : ℍ → ℂ} {F : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp Γ.subtype) F := by
  intro γ
  have hslash := hF.slash (γ : SL(2, ℤ))
  rw [hf _ γ.2] at hslash
  obtain ⟨v, hv⟩ := hslash.exists_sub_eq_const hF
  refine ⟨binaryFormRepSL ℂ n (γ : SL(2, ℤ)) v, fun τ => ?_⟩
  change F ((γ : SL(2, ℤ)) • τ) - binaryFormRepSL ℂ n (γ : SL(2, ℤ)) (F τ) = _
  rw [← hv τ, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F :=
  HeckeEis.SolMain.p1b hF hf

