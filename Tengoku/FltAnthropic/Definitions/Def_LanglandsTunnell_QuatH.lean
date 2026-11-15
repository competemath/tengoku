import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_SylowH
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.NumberTheory.NumberField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FLT.ExplicitLift LanglandsTunnell.Lift48
open scoped MatrixGroups

variable {L : Type} [Field L] [NumberField L]

abbrev fixFld (H : Subgroup (L ≃ₐ[ℚ] L)) : IntermediateField ℚ L :=
  FixedPoints.intermediateField (↥H)

/--
@isnad1 id=le.1h3v.s8.0281647b85c0 from=translated src=- shape=62cd5962 vocab=e1c336dd
-/
theorem fixFld_le_fixFld_of_le {H H' : Subgroup (L ≃ₐ[ℚ] L)} (h : H' ≤ H) :
    fixFld H ≤ fixFld H' := by
  intro x hx
  rw [fixFld, FixedPoints.mem_intermediateField_iff] at hx ⊢
  exact fun g => hx ⟨g.1, h g.2⟩

def detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  (Matrix.GeneralLinearGroup.det.comp e.toMonoidHom).ker

/--
@isnad1 id=iff.0h3v.s10.fb4809bd6fd4 from=translated src=- shape=5916ed05 vocab=b076b8a1
-/
theorem mem_detKer_iff (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (γ : L ≃ₐ[ℚ] L) :
    γ ∈ detKer e ↔
      ((e γ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
  rw [detKer, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Units.val_eq_one]
  rfl

/--
@isnad1 id=normal.0h2v.s8.3af026de4a3f from=translated src=- shape=2cff2190 vocab=8bda5ef6
-/
instance detKer_normal (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : (detKer e).Normal := by
  unfold detKer; infer_instance

def quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  sylowH e ⊓ detKer e

/--
@isnad1 id=le.0h2v.s9.7ffb704ffe07 from=translated src=- shape=6a67c2b3 vocab=da979359
-/
theorem quatH_le_sylowH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ sylowH e :=
  inf_le_left

/--
@isnad1 id=le.0h2v.s9.8216189c93a7 from=translated src=- shape=6a67c2b3 vocab=3179fcb5
-/
theorem quatH_le_detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ detKer e :=
  inf_le_right

/--
@isnad1 id=le.0h2v.s8.9a9bfc1e1744 from=translated src=- shape=c54a6921 vocab=362fbacb
-/
theorem fixFld_sylowH_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (sylowH e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_sylowH e)

/--
@isnad1 id=le.0h2v.s8.869ca1ab21b8 from=translated src=- shape=c54a6921 vocab=02e4b210
-/
theorem fixFld_detKer_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (detKer e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_detKer e)

section TowerInstances

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldQuatH :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_quatH e)).toRingHom.toAlgebra

/--
@isnad1 id=isscalar.0h2v.s9.58c6d4faa3ad from=translated src=- shape=ced2e226 vocab=c1208034
-/
instance isScalarTower_rat_fixFldSylowH_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/--
@isnad1 id=isscalar.0h2v.s9.68bec7feea71 from=translated src=- shape=5af864b4 vocab=c1208034
-/
instance isScalarTower_fixFldSylowH_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_quatH e) x).symm)

noncomputable instance algebra_fixFldDetKer_fixFldQuatH :
    Algebra ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_detKer_le_fixFld_quatH e)).toRingHom.toAlgebra

/--
@isnad1 id=isscalar.0h2v.s9.eb49838c9d52 from=translated src=- shape=ced2e226 vocab=3f036c94
-/
instance isScalarTower_rat_fixFldDetKer_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/--
@isnad1 id=isscalar.0h2v.s9.2603e95b7ca2 from=translated src=- shape=5af864b4 vocab=3f036c94
-/
instance isScalarTower_fixFldDetKer_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_detKer_le_fixFld_quatH e) x).symm)

end TowerInstances

section SynthProbe

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))
end SynthProbe

end LanglandsTunnell
