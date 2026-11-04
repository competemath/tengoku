/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.Adjunction.Additive
import Tengoku.Seed.CategoryTheory.Adjunction.Limits
import Tengoku.Seed.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Tengoku.Seed.CategoryTheory.ObjectProperty.ColimitsOfShape
import Tengoku.Seed.CategoryTheory.Preadditive.Yoneda.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact objects in a preadditive category

The vocabulary of Appendix A.2 of arXiv:2607.28411v1 that needs no triangulated structure,
following A.9 and A.10 literally:

* `Functor.PreservesSmallCoproducts` means preservation of all coproducts indexed in a fixed
  universe;
* `IsCompactObject` means that `Hom(K, -)` preserves those coproducts;
* `ObjectProperty.compactObjects` is the resulting object property, closed under
  isomorphisms;
* a left adjoint to a small-coproduct-preserving functor carries compact objects to compact
  objects.

The coproduct-and-extension closure `Coprod(G)` and compactly generated t-structures need
distinguished triangles and live in `CategoryTheory/Triangulated/CompactlyGenerated.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u₁ u₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- A functor preserves the coproducts indexed by types in universe `w`.

Keeping the indexing universe explicit matches Mathlib's universe-sensitive
colimit API and avoids pretending that one category has literally all
large-universe coproducts.-/
def PreservesSmallCoproducts (F : Functor C D) : Prop :=
  ∀ (ι : Type w), PreservesColimitsOfShape (Discrete ι) F

end Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Definition A.9: `K` is compact when `Hom(K, -)` preserves all small
coproducts in the indexing universe `w`.

The Hom functor is valued in additive commutative groups, so the colimit on
the target side is the direct sum of Hom groups.  Using ordinary set-valued
coyoneda here would instead form a disjoint union of Hom sets, which is not
the triangulated notion of compactness.-/
def IsCompactObject (K : C) : Prop :=
  ∀ (ι : Type w),
    PreservesColimitsOfShape (Discrete ι) (preadditiveCoyoneda.obj (op K))

namespace IsCompactObject

variable {K : C} (hK : IsCompactObject.{w} K)

/-- The defining compactness comparison: maps from `K` into a coproduct form
the direct sum of the Hom groups into its summands.-/
noncomputable def coproductComparisonIso {ι : Type w} (X : ι → C)
    [HasCoproduct X]
    [HasColimit (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K))] :
    (preadditiveCoyoneda.obj (op K)).obj (∐ X) ≅
      colimit (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K)) := by
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  exact preservesColimitIso (preadditiveCoyoneda.obj (op K))
    (Discrete.functor X)

/-- Under the compactness comparison, postcomposition with a coproduct
injection is the corresponding direct-sum injection.
@isnad1 id=eq.1h5v.s8.1503944a891e from=translated src=- shape=e56ee644 vocab=6f3ab199
-/
@[reassoc (attr := simp)]
theorem map_ι_coproductComparisonIso_hom {ι : Type w} (X : ι → C)
    [HasCoproduct X]
    [HasColimit (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K))]
    (i : ι) :
    (preadditiveCoyoneda.obj (op K)).map (Sigma.ι X i) ≫
      (hK.coproductComparisonIso X).hom =
        colimit.ι (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K))
          ⟨i⟩ := by
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  exact ι_preservesColimitIso_hom
    (preadditiveCoyoneda.obj (op K)) (Discrete.functor X) ⟨i⟩

end IsCompactObject

namespace ObjectProperty

/-- The object property of compact objects.-/
def compactObjects : ObjectProperty C := fun K ↦ IsCompactObject.{w} K

/-- Compactness is invariant under isomorphism.
@isnad1 id=iscompac.1h4v.s4.0a91b08399d6 from=translated src=- shape=848c34ab vocab=7c139977
-/
theorem isCompactObject_of_iso {K K' : C} (e : K ≅ K')
    (hK : IsCompactObject.{w} K) : IsCompactObject.{w} K' := by
  intro ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  exact preservesColimitsOfShape_of_natIso
    (preadditiveCoyoneda.mapIso e.symm.op)

end ObjectProperty

namespace Adjunction

variable {C : Type u₁} [Category.{v} C] [Preadditive C]
  {D : Type u₂} [Category.{v} D] [Preadditive D]
  {L : Functor D C} {F : Functor C D} [L.Additive]

/-- A left adjoint to a small-coproduct-preserving functor carries compact
objects to compact objects. This is the compactness step in A.16 and A.17.
@isnad1 id=iscompac.2h6v.s6.86e579bf1d3f from=translated src=- shape=3ab9252a vocab=cdab792e
-/
theorem isCompactObject_leftAdjoint_obj (adj : L ⊣ F)
    (hF : F.PreservesSmallCoproducts.{w}) {K : D}
    (hK : IsCompactObject.{w} K) : IsCompactObject.{w} (L.obj K) := by
  intro ι
  letI : PreservesColimitsOfShape (Discrete ι) F := hF ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  haveI : PreservesColimitsOfShape (Discrete ι)
      (F ⋙ preadditiveCoyoneda.obj (op K)) := inferInstance
  let e : preadditiveCoyoneda.obj (op (L.obj K)) ≅
      F ⋙ preadditiveCoyoneda.obj (op K) :=
    NatIso.ofComponents
      (fun X ↦ (adj.homAddEquiv K X).toAddCommGrpIso)
      (fun f ↦ by
        ext g
        exact adj.homEquiv_naturality_right g f)
  exact preservesColimitsOfShape_of_natIso e.symm

/-- The essential image under a left adjoint of compact objects is compact
when the right adjoint preserves small coproducts.
@isnad1 id=le.2h6v.s6.5377508b54a7 from=translated src=- shape=dded5fb4 vocab=4bbf7b03
-/
theorem compactObjects_map_leftAdjoint (adj : L ⊣ F)
    (hF : F.PreservesSmallCoproducts.{w}) {G : ObjectProperty D}
    (hG : G ≤ ObjectProperty.compactObjects.{w} (C := D)) :
    G.map L ≤ ObjectProperty.compactObjects.{w} (C := C) := by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact ObjectProperty.isCompactObject_of_iso e
    (adj.isCompactObject_leftAdjoint_obj hF (hG Y hY))

end Adjunction

end CategoryTheory
