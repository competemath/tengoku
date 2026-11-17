import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEichlerIntegral_smul.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEichlerIntegral_smul

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm IsEichlerIntegral)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups ModularForm

/--
@isnad1 id=iseichle.1h4v.s10.ee077244a2b4 from=translated src=- shape=235f9d6c vocab=6b7c70f6
-/
theorem SolMain.smul {n : ℕ} {f : ℍ → ℂ} {F : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (c : ℂ) :
    IsEichlerIntegral n (c • f) (c • F) := by
  intro d τ
  have h := (hF d τ).const_mul c
  rw [← mul_assoc] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, Submodule.coe_smul, coeff_smul, smul_eq_mul]

end HeckeEis

end

open scoped MatrixGroups ModularForm in
/--
@isnad1 id=iseichle.1h4v.s10.ee077244a2b4 from=translated src=- shape=235f9d6c vocab=6b7c70f6
-/
theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (c : ℂ) :
    HeckeEis.IsEichlerIntegral n (c • f) (c • F) :=
  HeckeEis.SolMain.smul hF c

