import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEichlerIntegral_add.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEichlerIntegral_add

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm IsEichlerIntegral)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace SolMain

private theorem _root_.HeckeEis.SolMain.add {n : ℕ} {f g : ℍ → ℂ} {F G : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (hG : IsEichlerIntegral n g G) :
    IsEichlerIntegral n (f + g) (F + G) := by
  intro d τ
  have h := (hF d τ).add (hG d τ)
  simp only [← add_mul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, Submodule.coe_add, coeff_add]

end SolMain
export _root_.HeckeEis (SolMain.add)
end HeckeEis

end

open scoped MatrixGroups ModularForm in
/--
@isnad1 id=iseichle.2h5v.s10.c59cfdcb37bc from=translated src=- shape=b1377e6f vocab=3cd50508
-/
theorem solution {n : ℕ} {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) :=
  HeckeEis.SolMain.add hF hG

