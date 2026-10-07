/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.OpenImmersion

/-!

# Being an isomorphism is local at the target

-/

universe u

public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

/--
@isnad1 id=iff.0h3v.s4.74b9c4399bf5 from=seed src=0 shape=e28b86d4 vocab=817c5dab
-/
lemma isIso_iff_isOpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Surjective f := by
  rw [surjective_iff, ← TopCat.epi_iff_surjective, isIso_iff_isOpenImmersion_and_epi_base]

/--
@isnad1 id=eq.0h0v.s5.a62bdb3ae25f from=seed src=0 shape=81f0a72d vocab=9b44e71e
-/
lemma isomorphisms_eq_isOpenImmersion_inf_surjective :
    isomorphisms Scheme = (@IsOpenImmersion ⊓ @Surjective : MorphismProperty Scheme) := by
  ext
  rw [isomorphisms.iff, isIso_iff_isOpenImmersion_and_surjective]
  rfl

/--
@isnad1 id=eq.0h0v.s7.fb7f1a939ef4 from=seed src=0 shape=27cfde14 vocab=1492c38a
-/
lemma isomorphisms_eq_stalkwise :
    isomorphisms Scheme = (isomorphisms TopCat).inverseImage Scheme.forgetToTop ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective, isOpenImmersion_eq_inf,
    surjective_eq_topologically, inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H ↦ inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) ↦
    let e := (TopCat.homeoOfIso <| asIso f.base); ⟨e.isOpenEmbedding, e.surjective⟩⟩

example : IsZariskiLocalAtTarget (isomorphisms Scheme) := inferInstance

set_option backward.isDefEq.respectTransparency false in
instance : HasAffineProperty (isomorphisms Scheme) fun X _ f _ ↦ IsAffine X ∧ IsIso (f.appTop) := by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ ↦ (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop)))),
    fun (_ : IsIso f) ↦ ⟨.of_isIso f, inferInstance⟩⟩

instance : IsZariskiLocalAtTarget (monomorphisms Scheme) :=
  diagonal_isomorphisms (C := Scheme).symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h3v.s6.6f43f00609d7 from=seed src=0 shape=52bf8580 vocab=610d5694
-/
lemma isIso_SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    IsIso (Spec.map f) ↔ Function.Bijective f.hom := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  rw [← isomorphisms.iff, (isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f),
    isomorphisms.iff]
  infer_instance

end AlgebraicGeometry
