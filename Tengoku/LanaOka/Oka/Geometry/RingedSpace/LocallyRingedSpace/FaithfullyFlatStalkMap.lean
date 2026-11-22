/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Geometry.RingedSpace.OpenImmersion
import Tengoku.Seed.RingTheory.RingHom.FaithfullyFlat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Faithfully flat stalk maps of morphisms of locally ringed spaces

Faithful flatness of the stalk map of a morphism of locally ringed spaces at a point is stable
under composition, holds for morphisms whose stalk map is an isomorphism (e.g. open immersions),
and can be cancelled against such morphisms on the left.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.faithfullyFlat_stalkMap_comp`: composition.
- `AlgebraicGeometry.LocallyRingedSpace.faithfullyFlat_stalkMap_of_isIso`: isomorphisms on stalks,
  in particular open immersions and isomorphisms.
- `AlgebraicGeometry.LocallyRingedSpace.faithfullyFlat_stalkMap_of_comp`: if `ι ≫ f` has a
  faithfully flat stalk map at `x` and `ι` is an isomorphism on stalks at `x`, then `f` has a
  faithfully flat stalk map at `ι x`; `faithfullyFlat_stalkMap_of_comp_eq_right` is the same on
  the other side.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}

/-- An isomorphism of commutative rings is faithfully flat.
@isnad1 id=faithful.0h3v.s5.377034046985 from=translated src=- shape=44821570 vocab=62ce3d4b
-/
theorem _root_.CommRingCat.faithfullyFlat_hom_of_isIso {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsIso f] : f.hom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.of_bijective (ConcreteCategory.bijective_of_isIso f)

/-- **Faithfully flat stalk maps compose.**
@isnad1 id=faithful.2h6v.s11.d365f678d5e1 from=translated src=- shape=25df2f97 vocab=82ba4c3b
-/
theorem faithfullyFlat_stalkMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : (f.stalkMap x).hom.FaithfullyFlat) (hg : (g.stalkMap (f.base x)).hom.FaithfullyFlat) :
    ((f ≫ g).stalkMap x).hom.FaithfullyFlat := by
  rw [stalkMap_comp]
  exact RingHom.FaithfullyFlat.stableUnderComposition (g.stalkMap (f.base x)).hom
    (f.stalkMap x).hom hg hf

/-- A morphism which is an isomorphism on the stalk at `x` has a faithfully flat stalk map
at `x`; this applies to open immersions and isomorphisms.
@isnad1 id=faithful.0h4v.s9.19c98302b81d from=translated src=- shape=d459ec8b vocab=5ef3ab08
-/
theorem faithfullyFlat_stalkMap_of_isIso (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    (f.stalkMap x).hom.FaithfullyFlat :=
  CommRingCat.faithfullyFlat_hom_of_isIso _

/-- An open immersion has faithfully flat stalk maps.
@isnad1 id=faithful.0h4v.s9.205ed8adfa1c from=translated src=- shape=dbb4f2bc vocab=6bbc7d02
-/
theorem faithfullyFlat_stalkMap_of_isOpenImmersion (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] (x : X) : (f.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isIso f x

/-- An isomorphism of locally ringed spaces has faithfully flat stalk maps.
@isnad1 id=faithful.0h4v.s9.86b6fda3b29d from=translated src=- shape=242e373a vocab=5ef3ab08
-/
theorem faithfullyFlat_stalkMap_of_isIso_hom (f : X ⟶ Y) [IsIso f] (x : X) :
    (f.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isOpenImmersion f x

/-- The forward map of an isomorphism of locally ringed spaces has faithfully flat stalk
maps.
@isnad1 id=faithful.0h4v.s9.ade63a4e805b from=translated src=- shape=4e1fe9f5 vocab=e253e7a8
-/
theorem faithfullyFlat_stalkMap_iso_hom (e : X ≅ Y) (x : X) :
    (e.hom.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isIso_hom e.hom x

/-- **Cancelling an isomorphism on stalks**: if `ι ≫ f` has a faithfully flat stalk map at `x`
and the stalk map of `ι` at `x` is an isomorphism, then `f` has a faithfully flat stalk map at
`ι x`.
@isnad1 id=faithful.1h6v.s11.ee7a5d684179 from=translated src=- shape=f68c071f vocab=69396efa
-/
theorem faithfullyFlat_stalkMap_of_comp (ι : X ⟶ Y) (f : Y ⟶ Z) (x : X)
    [IsIso (ι.stalkMap x)] (h : ((ι ≫ f).stalkMap x).hom.FaithfullyFlat) :
    (f.stalkMap (ι.base x)).hom.FaithfullyFlat := by
  have e : f.stalkMap (ι.base x) = (ι ≫ f).stalkMap x ≫ inv (ι.stalkMap x) := by
    rw [stalkMap_comp]; simp
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition ((ι ≫ f).stalkMap x).hom
    (inv (ι.stalkMap x)).hom h (CommRingCat.faithfullyFlat_hom_of_isIso _)

/-- `AlgebraicGeometry.LocallyRingedSpace.faithfullyFlat_stalkMap_of_comp`, for a morphism
`g` which is equal to `ι ≫ f`.
@isnad1 id=faithful.2h7v.s11.61dc2c2024a0 from=translated src=- shape=4542c024 vocab=69396efa
-/
theorem faithfullyFlat_stalkMap_of_comp_eq (ι : X ⟶ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (e : ι ≫ f = g) (x : X) [IsIso (ι.stalkMap x)] (h : (g.stalkMap x).hom.FaithfullyFlat) :
    (f.stalkMap (ι.base x)).hom.FaithfullyFlat := by
  subst e
  exact faithfullyFlat_stalkMap_of_comp ι f x h

/-- **Cancelling an isomorphism on stalks on the right**: if `f ≫ j = g`, the stalk map of `g`
at `x` is faithfully flat and the stalk map of `j` at `f x` is an isomorphism, then `f` has a
faithfully flat stalk map at `x`.
@isnad1 id=faithful.2h7v.s10.e7169fcf7132 from=translated src=- shape=ad248b8d vocab=69396efa
-/
theorem faithfullyFlat_stalkMap_of_comp_eq_right (f : X ⟶ Y) (j : Y ⟶ Z) (g : X ⟶ Z)
    (e : f ≫ j = g) (x : X) [IsIso (j.stalkMap (f.base x))]
    (h : (g.stalkMap x).hom.FaithfullyFlat) : (f.stalkMap x).hom.FaithfullyFlat := by
  subst e
  have e : f.stalkMap x = inv (j.stalkMap (f.base x)) ≫ (f ≫ j).stalkMap x := by
    rw [stalkMap_comp]; simp
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition (inv (j.stalkMap (f.base x))).hom
    ((f ≫ j).stalkMap x).hom (CommRingCat.faithfullyFlat_hom_of_isIso _) h

end AlgebraicGeometry.LocallyRingedSpace
