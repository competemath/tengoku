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

/-- An isomorphism of commutative rings is faithfully flat. -/
theorem _root_.CommRingCat.faithfullyFlat_hom_of_isIso {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsIso f] : f.hom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.of_bijective (ConcreteCategory.bijective_of_isIso f)

/-- **Faithfully flat stalk maps compose.** -/
theorem faithfullyFlat_stalkMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : (f.stalkMap x).hom.FaithfullyFlat) (hg : (g.stalkMap (f.base x)).hom.FaithfullyFlat) :
    ((f ≫ g).stalkMap x).hom.FaithfullyFlat := by
  rw [stalkMap_comp]
  exact RingHom.FaithfullyFlat.stableUnderComposition (g.stalkMap (f.base x)).hom
    (f.stalkMap x).hom hg hf

/-- A morphism which is an isomorphism on the stalk at `x` has a faithfully flat stalk map
at `x`; this applies to open immersions and isomorphisms. -/
theorem faithfullyFlat_stalkMap_of_isIso (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    (f.stalkMap x).hom.FaithfullyFlat :=
  CommRingCat.faithfullyFlat_hom_of_isIso _

/-- An open immersion has faithfully flat stalk maps. -/
theorem faithfullyFlat_stalkMap_of_isOpenImmersion (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] (x : X) : (f.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isIso f x

/-- An isomorphism of locally ringed spaces has faithfully flat stalk maps. -/
theorem faithfullyFlat_stalkMap_of_isIso_hom (f : X ⟶ Y) [IsIso f] (x : X) :
    (f.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isOpenImmersion f x

/-- The forward map of an isomorphism of locally ringed spaces has faithfully flat stalk
maps. -/
theorem faithfullyFlat_stalkMap_iso_hom (e : X ≅ Y) (x : X) :
    (e.hom.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isIso_hom e.hom x

/-- **Cancelling an isomorphism on stalks**: if `ι ≫ f` has a faithfully flat stalk map at `x`
and the stalk map of `ι` at `x` is an isomorphism, then `f` has a faithfully flat stalk map at
`ι x`. -/
theorem faithfullyFlat_stalkMap_of_comp (ι : X ⟶ Y) (f : Y ⟶ Z) (x : X)
    [IsIso (ι.stalkMap x)] (h : ((ι ≫ f).stalkMap x).hom.FaithfullyFlat) :
    (f.stalkMap (ι.base x)).hom.FaithfullyFlat := by
  have e : f.stalkMap (ι.base x) = (ι ≫ f).stalkMap x ≫ inv (ι.stalkMap x) := by
    rw [stalkMap_comp]; simp
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition ((ι ≫ f).stalkMap x).hom
    (inv (ι.stalkMap x)).hom h (CommRingCat.faithfullyFlat_hom_of_isIso _)

/-- `AlgebraicGeometry.LocallyRingedSpace.faithfullyFlat_stalkMap_of_comp`, for a morphism
`g` which is equal to `ι ≫ f`. -/
theorem faithfullyFlat_stalkMap_of_comp_eq (ι : X ⟶ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (e : ι ≫ f = g) (x : X) [IsIso (ι.stalkMap x)] (h : (g.stalkMap x).hom.FaithfullyFlat) :
    (f.stalkMap (ι.base x)).hom.FaithfullyFlat := by
  subst e
  exact faithfullyFlat_stalkMap_of_comp ι f x h

/-- **Cancelling an isomorphism on stalks on the right**: if `f ≫ j = g`, the stalk map of `g`
at `x` is faithfully flat and the stalk map of `j` at `f x` is an isomorphism, then `f` has a
faithfully flat stalk map at `x`. -/
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
