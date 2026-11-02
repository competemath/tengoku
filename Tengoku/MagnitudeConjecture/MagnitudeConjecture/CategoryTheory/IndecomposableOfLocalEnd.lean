import Tengoku
import Tengoku.Seed.CategoryTheory.Preadditive.AdditiveFunctor
import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Categorical indecomposability from a local endomorphism ring

In a preadditive category with binary biproducts, a local endomorphism ring
forces categorical indecomposability.  This is a bounded adaptation of the
generic lemma in the donor's
`RepresentationDirected/IyamaWordMeshAdditiveHull.lean` at commit
`d5ba0c48e7a851afd51247ff9cd81fc629e00ed2`; no word-mesh layer is imported.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe v u

/-- Categorical indecomposability is invariant under isomorphism.-/
theorem indecomposable_iff_of_iso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] {X Y : C} (e : X ≅ Y) :
    Indecomposable X ↔ Indecomposable Y := by
  constructor
  · rintro ⟨hX0, hX⟩
    refine ⟨?_, ?_⟩
    · intro hY0
      exact hX0 ((e.isZero_iff).2 hY0)
    · intro Z W hYW
      exact hX Z W (e.trans hYW)
  · rintro ⟨hY0, hY⟩
    refine ⟨?_, ?_⟩
    · intro hX0
      exact hY0 ((e.isZero_iff).1 hX0)
    · intro Z W hXW
      exact hY Z W (e.symm.trans hXW)

/-- Passing to the opposite category preserves and reflects categorical
indecomposability.-/
theorem indecomposable_op_iff
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] (X : C) :
    Indecomposable (Opposite.op X) ↔ Indecomposable X := by
  constructor
  · rintro ⟨hX0, hX⟩
    refine ⟨fun hzero ↦ hX0 hzero.op, ?_⟩
    intro Y Z e
    let eop : Opposite.op X ≅ Opposite.op Y ⊞ Opposite.op Z :=
      e.op.symm ≪≫ biprod.opIso Y Z
    rcases hX _ _ eop with hY | hZ
    · exact Or.inl hY.unop
    · exact Or.inr hZ.unop
  · rintro ⟨hX0, hX⟩
    refine ⟨fun hzero ↦ hX0 hzero.unop, ?_⟩
    intro Y Z e
    rcases Y with ⟨Y⟩
    rcases Z with ⟨Z⟩
    let eunop : X ≅ Y ⊞ Z :=
      e.unop.symm ≪≫ (biprod.opIso Y Z).unop
    rcases hX _ _ eunop with hY | hZ
    · exact Or.inl hY.op
    · exact Or.inr hZ.op

universe v' u'

/-- A fully faithful additive functor reflects indecomposability from the
image of an object.-/
theorem indecomposable_of_fully_faithful_additive
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (X : C) (hX : Indecomposable (F.obj X)) : Indecomposable X := by
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  constructor
  · intro hzero
    exact hX.1 (F.map_isZero hzero)
  · intro Y Z e
    let e' : F.obj X ≅ F.obj Y ⊞ F.obj Z :=
      F.mapIso e ≪≫ F.mapBiprod Y Z
    rcases hX.2 _ _ e' with hY | hZ
    · exact Or.inl (IsZero.of_full_of_faithful_of_isZero F Y hY)
    · exact Or.inr (IsZero.of_full_of_faithful_of_isZero F Z hZ)

/-- An additive equivalence preserves and reflects indecomposability.-/
theorem indecomposable_map_iff_of_equivalence
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] (X : C) :
    Indecomposable (F.obj X) ↔ Indecomposable X := by
  constructor
  · exact indecomposable_of_fully_faithful_additive F X
  · intro hX
    let E := F.asEquivalence
    letI : E.functor.Additive := inferInstanceAs F.Additive
    letI : E.inverse.Additive :=
      { map_add := fun {X Y} f g ↦
          E.functor.map_injective (by
            rw [E.functor.map_add]
            simp) }
    have hInv : Indecomposable (E.inverse.obj (F.obj X)) :=
      (indecomposable_iff_of_iso (E.unitIso.app X)).mp hX
    exact indecomposable_of_fully_faithful_additive E.inverse
      (F.obj X) hInv

end MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RingEquiv

universe u₁ u₂

/-- Localness transports across a ring equivalence without a commutativity
hypothesis.-/
theorem isLocalRing_noncomm {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    [IsLocalRing R] (e : R ≃+* S) : IsLocalRing S := by
  letI : Nontrivial S := e.injective.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro s
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
    (R := R) (a := e.symm s) (b := 1 - e.symm s)
    (add_sub_cancel (e.symm s) 1) with h | h
  · exact Or.inl (by simpa using h.map e)
  · exact Or.inr (by simpa using h.map e)

end MagnitudeConjecture.RingEquiv
