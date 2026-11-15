import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_CurveModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicCurve

section FunctionFieldIso

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem inv_base_genericPoint (e : X ≅ Y) : e.inv.base (genericPoint Y) = genericPoint X :=
  genericPoint_eq_of_isOpenImmersion e.inv

theorem hom_base_genericPoint (e : X ≅ Y) : e.hom.base (genericPoint X) = genericPoint Y :=
  genericPoint_eq_of_isOpenImmersion e.hom

def functionFieldHomOfIso (e : X ≅ Y) : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes (specializes_of_eq (inv_base_genericPoint e)) ≫ e.inv.stalkMap (genericPoint Y)

private theorem isIso_stalkSpecializes_of_eq {Z : Scheme.{u}} {x y : Z} (h : x = y) :
    IsIso (Z.presheaf.stalkSpecializes (specializes_of_eq h)) := by
  subst h
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

instance isIso_functionFieldHomOfIso (e : X ≅ Y) : IsIso (functionFieldHomOfIso e) := by
  haveI := isIso_stalkSpecializes_of_eq (inv_base_genericPoint e)
  exact IsIso.comp_isIso

def functionFieldIsoOfIso (e : X ≅ Y) : X.functionField ≃+* Y.functionField :=
  (asIso (functionFieldHomOfIso e)).commRingCatIsoToRingEquiv

theorem functionFieldIsoOfIso_apply (e : X ≅ Y) (z : X.functionField) :
    functionFieldIsoOfIso e z = (functionFieldHomOfIso e).hom z := rfl

theorem ofHom_functionFieldIsoOfIso (e : X ≅ Y) :
    CommRingCat.ofHom (functionFieldIsoOfIso e).toRingHom = functionFieldHomOfIso e :=
  CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

theorem fromSpecStalk_comp_inv_eq_specMap_functionFieldIsoOfIso (e : X ≅ Y) :
    Y.fromSpecStalk (genericPoint Y) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (functionFieldIsoOfIso e).toRingHom) ≫ X.fromSpecStalk (genericPoint X) := by
  rw [ofHom_functionFieldIsoOfIso, functionFieldHomOfIso, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem fromSpecStalk_eq_specMap_functionFieldIsoOfIso_comp_hom (e : X ≅ Y) :
    Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom (functionFieldIsoOfIso e).toRingHom) ≫ X.fromSpecStalk (genericPoint X) ≫ e.hom := by
  rw [← Category.assoc, ← fromSpecStalk_comp_inv_eq_specMap_functionFieldIsoOfIso, Category.assoc, e.inv_hom_id,
    Category.comp_id]

theorem stalkToFunctionField_comp_functionFieldHomOfIso (e : X ≅ Y) (y : Y) :
    X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ (e.inv.base y))) ≫
        functionFieldHomOfIso e =
      e.inv.stalkMap y ≫ Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y)) := by
  rw [functionFieldHomOfIso, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap e.inv (genericPoint Y) y ((genericPoint_spec Y).specializes (Set.mem_univ y))

theorem functionFieldIsoOfIso_algebraMap_stalk (e : X ≅ Y) (y : Y) (s : X.presheaf.stalk (e.inv.base y)) :
    functionFieldIsoOfIso e (algebraMap (X.presheaf.stalk (e.inv.base y)) X.functionField s) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (e.inv.stalkMap y s) := by
  have h := stalkToFunctionField_comp_functionFieldHomOfIso e y
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CategoryTheory.comp_apply] at h'
  exact h'

end FunctionFieldIso

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

section ClosedPoints

variable {X Y : Scheme.{u}}

private theorem mem_closedPoints_of_iso {Z W : Scheme.{u}} (f : Z ⟶ W) [IsIso f] {z : Z} (hz : z ∈ closedPoints Z) :
    f.base z ∈ closedPoints W := by
  have h : IsClosed (f.base '' {z}) := f.isClosedEmbedding.isClosedMap _ hz
  rwa [Set.image_singleton] at h

def closedPointsEquivOfIso (e : X ≅ Y) : closedPoints Y ≃ closedPoints X where
  toFun y := ⟨e.inv.base y.1, mem_closedPoints_of_iso e.inv y.2⟩
  invFun x := ⟨e.hom.base x.1, mem_closedPoints_of_iso e.hom x.2⟩
  left_inv y := Subtype.ext (by
    show (e.inv ≫ e.hom).base y.1 = y.1
    rw [e.inv_hom_id]; rfl)
  right_inv x := Subtype.ext (by
    show (e.hom ≫ e.inv).base x.1 = x.1
    rw [e.hom_inv_id]; rfl)

@[simp] theorem closedPointsEquivOfIso_apply_coe (e : X ≅ Y) (y : closedPoints Y) :
    ((closedPointsEquivOfIso e y : closedPoints X) : X) = e.inv.base y.1 := rfl

end ClosedPoints

section Transport

variable (Mdl : CurveModel K L) {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) (e : Mdl.C ≅ C)
  (he : e.hom ≫ c = Mdl.toBase)

end Transport

end CurveModel

end AlgebraicCurve

end
