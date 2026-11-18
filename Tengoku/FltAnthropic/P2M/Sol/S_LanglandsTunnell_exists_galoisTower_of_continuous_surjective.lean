import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_GalRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
export _root_.LanglandsTunnell (galRep galRep_apply)
namespace P4
namespace TowerSol
open _root_.LanglandsTunnell

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

variable (ρ : Γℚ →* GL (Fin 2) (ZMod 3))

/--
@isnad1 id=isclosed.1h1v.s11.974cd8510a4b from=translated src=- shape=7d6a1043 vocab=4dc05900
-/
theorem isClosed_ker (hcont : Continuous ρ) : IsClosed (ρ.ker : Set Γℚ) := by
  have : (ρ.ker : Set Γℚ) = ρ ⁻¹' {1} := by ext σ; exact MonoidHom.mem_ker
  rw [this]
  exact (isClosed_discrete _).preimage hcont

/--
@isnad1 id=isopen.1h1v.s11.a079a4d9dc7d from=translated src=- shape=7d6a1043 vocab=3512fd00
-/
theorem isOpen_ker (hcont : Continuous ρ) : IsOpen (ρ.ker : Set Γℚ) := by
  have : (ρ.ker : Set Γℚ) = ρ ⁻¹' {1} := by ext σ; exact MonoidHom.mem_ker
  rw [this]
  exact (isOpen_discrete _).preimage hcont

def kerClosed (hcont : Continuous ρ) : ClosedSubgroup Γℚ := ⟨ρ.ker, isClosed_ker ρ hcont⟩

/--
@isnad1 id=normal.1h1v.s11.b914fb5346af from=translated src=- shape=53a91178 vocab=ebace567
-/
scoped instance kerClosed_normal (hcont : Continuous ρ) : (kerClosed ρ hcont).1.Normal :=
  inferInstanceAs ρ.ker.Normal

abbrev levelField (hcont : Continuous ρ) : IntermediateField ℚ ℚbar :=
  IntermediateField.fixedField (kerClosed ρ hcont).1

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h1v.s11.a3d5dbf600fe from=translated src=- shape=28cfd7c1 vocab=9859790b
-/
theorem fixingSubgroup_levelField (hcont : Continuous ρ) :
    (levelField ρ hcont).fixingSubgroup = ρ.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (kerClosed ρ hcont)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=and.1h1v.s11.1a90884c5e33 from=translated src=- shape=6a32df31 vocab=c05b2e23
-/
theorem finiteDimensional_and_isGalois_levelField (hcont : Continuous ρ) :
    FiniteDimensional ℚ (levelField ρ hcont) ∧ IsGalois ℚ (levelField ρ hcont) := by
  rw [← InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois, fixingSubgroup_levelField]
  exact ⟨isOpen_ker ρ hcont, inferInstance⟩

/--
@isnad1 id=finitedi.1h1v.s11.68aef21ed856 from=translated src=- shape=e2f26a16 vocab=d99a1638
-/
scoped instance finiteDimensional_levelField (hcont : Continuous ρ) : FiniteDimensional ℚ (levelField ρ hcont) :=
  (finiteDimensional_and_isGalois_levelField ρ hcont).1

/--
@isnad1 id=isgalois.1h1v.s11.327ffd8b088a from=translated src=- shape=e2f26a16 vocab=1d929b72
-/
scoped instance isGalois_levelField (hcont : Continuous ρ) : IsGalois ℚ (levelField ρ hcont) :=
  (finiteDimensional_and_isGalois_levelField ρ hcont).2

/--
@isnad1 id=numberfi.1h1v.s11.f2dff0e22d52 from=translated src=- shape=c8c1a9c0 vocab=f9161712
-/
scoped instance numberField_levelField (hcont : Continuous ρ) : NumberField (levelField ρ hcont) :=
  haveI : CharZero (levelField ρ hcont) := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  NumberField.mk

set_option backward.isDefEq.respectTransparency false in

def towerIso (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ((levelField ρ hcont) ≃ₐ[ℚ] (levelField ρ hcont)) ≃* GL (Fin 2) (ZMod 3) :=
  (InfiniteGalois.normalAutEquivQuotient (kerClosed ρ hcont)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)

set_option backward.isDefEq.respectTransparency false in

/--
@isnad1 id=eq.2h1v.s12.11ac9d822f21 from=translated src=- shape=dc8888a3 vocab=51f60f02
-/
theorem galRep_towerIso (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    LanglandsTunnell.galRep (towerIso ρ hcont hsurj) = ρ := by
  ext1 σ
  rw [LanglandsTunnell.galRep_apply]
  show (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)
      ((InfiniteGalois.normalAutEquivQuotient (kerClosed ρ hcont)).symm
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (levelField ρ hcont) σ)) = ρ σ
  rw [← InfiniteGalois.normalAutEquivQuotient_apply (kerClosed ρ hcont) σ, MulEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

/--
@isnad1 id=ex.2h1v.s14.7cc883d49db2 from=translated src=- shape=295a37c0 vocab=953319fa
-/
theorem exists_tower_of_continuous_surjective (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ∃ (L : IntermediateField ℚ ℚbar) (_ : NumberField ↥L) (_ : IsGalois ℚ ↥L)
      (e : (↥L ≃ₐ[ℚ] ↥L) ≃* GL (Fin 2) (ZMod 3)), LanglandsTunnell.galRep e = ρ :=
  ⟨levelField ρ hcont, inferInstance, inferInstance, towerIso ρ hcont hsurj, galRep_towerIso ρ hcont hsurj⟩

end LanglandsTunnell.P4.TowerSol
open scoped _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4 _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4.TowerSol
open scoped _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4
open scoped _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell

end
open scoped _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4 _root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.LanglandsTunnell.P4.TowerSol

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=ex.2h1v.s14.7cc883d49db2 from=translated src=- shape=295a37c0 vocab=953319fa
-/
theorem solution
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod 3))
    (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥L) (_ : IsGalois ℚ ↥L)
      (e : (↥L ≃ₐ[ℚ] ↥L) ≃* GL (Fin 2) (ZMod 3)), LanglandsTunnell.galRep e = ρ :=
  LanglandsTunnell.P4.TowerSol.exists_tower_of_continuous_surjective ρ hcont hsurj

