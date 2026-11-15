import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe w v u

namespace CategoryTheory.Functor

open Limits

variable {C : Type u} [Category.{v} C]

section Corepresentable

variable {F : C ⥤ Type w}

@[simps]
def corepresentableByOfIsInitial (e : F.Elements) (he : IsInitial e) :
    F.CorepresentableBy e.1 where
  homEquiv {Y} :=
    { toFun f := F.map f e.2
      invFun y := (he.to (F.elementsMk Y y)).val
      left_inv f := congrArg Subtype.val
        (he.hom_ext (he.to (F.elementsMk Y (F.map f e.2))) ⟨f, rfl⟩)
      right_inv y := (he.to (F.elementsMk Y y)).property }
  homEquiv_comp {Y Y'} g f := by simp [Functor.map_comp_apply]

/--
@isnad1 id=iscorepr.0h2v.s4.778c3424acfc from=translated src=- shape=01f3cc3b vocab=bdda5d6f
-/
lemma isCorepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsCorepresentable :=
  (corepresentableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isCorepresentable

/--
@isnad1 id=iff.0h2v.s4.d0079c909e0b from=translated src=- shape=1a1e9948 vocab=bdda5d6f
-/
lemma isCorepresentable_iff_hasInitial_elements :
    F.IsCorepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isCorepresentable_of_hasInitial_elements⟩

end Corepresentable

section Representable

variable {F : Cᵒᵖ ⥤ Type w}

@[simps]
def representableByOfIsInitial (e : F.Elements) (he : IsInitial e) :
    F.RepresentableBy e.1.unop where
  homEquiv {Y} :=
    { toFun f := F.map f.op e.2
      invFun y := (he.to (F.elementsMk (Opposite.op Y) y)).val.unop
      left_inv f := congrArg (fun g => Quiver.Hom.unop (Subtype.val g))
        (he.hom_ext (he.to (F.elementsMk (Opposite.op Y) (F.map f.op e.2))) ⟨f.op, rfl⟩)
      right_inv y := (he.to (F.elementsMk (Opposite.op Y) y)).property }
  homEquiv_comp {Y Y'} g f := by simp [Functor.map_comp_apply]

/--
@isnad1 id=isrepres.0h2v.s5.43f8e8380d26 from=translated src=- shape=5ca50901 vocab=07b29b2e
-/
lemma isRepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsRepresentable :=
  (representableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isRepresentable

/--
@isnad1 id=iff.0h2v.s5.6e10e9737739 from=translated src=- shape=c847f7ec vocab=07b29b2e
-/
lemma isRepresentable_iff_hasInitial_elements :
    F.IsRepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isRepresentable_of_hasInitial_elements⟩

end Representable

end CategoryTheory.Functor
