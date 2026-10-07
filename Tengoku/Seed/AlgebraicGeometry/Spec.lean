/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Geometry.RingedSpace.LocallyRingedSpace
public import Tengoku.Seed.AlgebraicGeometry.StructureSheaf
public import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization
public import Tengoku.Seed.Topology.Sheaves.SheafCondition.Sites
public import Tengoku.Seed.Topology.Sheaves.Functors
public import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.toTop`, valued in the category of topological spaces,
2. `Spec.toSheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.toLocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.toPresheafedSpace` as a composition of `Spec.toSheafedSpace` with
a forgetful functor.

## Related results

The adjunction `Γ ⊣ Spec` is constructed in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`.

-/

@[expose] public section


-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

/-- The spectrum of a commutative ring, as a topological space.
-/
def Spec.topObj (R : CommRingCat.{u}) : TopCat :=
  TopCat.of (PrimeSpectrum R)

/--
@isnad1 id=eq.0h1v.s5.e3f4e856b117 from=seed src=0 shape=aad5afd8 vocab=68dc6c53
-/
@[simp] theorem Spec.topObj_forget {R} : ToType (Spec.topObj R) = PrimeSpectrum R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def Spec.topMap {R S : CommRingCat.{u}} (f : R ⟶ S) : Spec.topObj S ⟶ Spec.topObj R :=
  TopCat.ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩

/--
@isnad1 id=eq.0h1v.s4.984c34dd17f2 from=seed src=0 shape=b11b3d58 vocab=d1840120
-/
@[simp]
theorem Spec.topMap_id (R : CommRingCat.{u}) : Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.21d2a8f95c40 from=seed src=0 shape=e9cd887f vocab=aff2a4ba
-/
@[simp]
theorem Spec.topMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.topMap (f ≫ g) = Spec.topMap g ≫ Spec.topMap f :=
  rfl

-- Porting note: `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps!]
def Spec.toTop : CommRingCat.{u}ᵒᵖ ⥤ TopCat where
  obj R := Spec.topObj (unop R)
  map {_ _} f := Spec.topMap f.unop

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def Spec.sheafedSpaceObj (R : CommRingCat.{u}) : SheafedSpace CommRingCat where
  carrier := Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

set_option backward.isDefEq.respectTransparency.types false in
/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps hom_base hom_c_app]
def Spec.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.sheafedSpaceObj S ⟶ Spec.sheafedSpaceObj R where
  hom.base := Spec.topMap f
  hom.c :=
    { app := fun U => CommRingCat.ofHom <|
        comap f.hom (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => by ext; rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h1v.s5.20ea2757eb71 from=seed src=0 shape=644a80b3 vocab=04f6fd56
-/
@[simp]
theorem Spec.sheafedSpaceMap_id {R : CommRingCat.{u}} :
    Spec.sheafedSpaceMap (𝟙 R) = 𝟙 (Spec.sheafedSpaceObj R) := by
  ext : 1
  · exact Spec.topMap_id R
  · ext
    dsimp
    rw [comap_id (by simp)]
    simp
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s6.b18b4b030ade from=seed src=0 shape=e457c0df vocab=e132b671
-/
theorem Spec.sheafedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.sheafedSpaceMap (f ≫ g) = Spec.sheafedSpaceMap g ≫ Spec.sheafedSpaceMap f := by
  ext : 1
  · exact Spec.topMap_comp f g
  · ext
    -- Porting note: was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app, sheafedSpaceMap_hom_c_app, Functor.whiskerRight_app, eqToHom_refl]
    erw [(sheafedSpaceObj T).presheaf.map_id]
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [comap_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def Spec.toSheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ SheafedSpace CommRingCat where
  obj R := Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_comp f g := by simp [Spec.sheafedSpaceMap_comp]

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.toPresheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ PresheafedSpace CommRingCat :=
  Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

/--
@isnad1 id=eq.0h1v.s4.42ad42551d8c from=seed src=0 shape=346b7e80 vocab=cf60c48a
-/
@[simp]
theorem Spec.toPresheafedSpace_obj (R : CommRingCat.{u}ᵒᵖ) :
    Spec.toPresheafedSpace.obj R = (Spec.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.616d4b5ea8a2 from=seed src=0 shape=aa20251e vocab=0a53b6ea
-/
theorem Spec.toPresheafedSpace_obj_op (R : CommRingCat.{u}) :
    Spec.toPresheafedSpace.obj (op R) = (Spec.sheafedSpaceObj R).toPresheafedSpace :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.174236e525a4 from=seed src=0 shape=fdd91726 vocab=ba1a8a32
-/
@[simp]
theorem Spec.toPresheafedSpace_map (R S : CommRingCat.{u}ᵒᵖ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f = (Spec.sheafedSpaceMap f.unop).hom :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.590775c830b7 from=seed src=0 shape=1608cd2d vocab=69025b4d
-/
theorem Spec.toPresheafedSpace_map_op (R S : CommRingCat.{u}) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f.op = (Spec.sheafedSpaceMap f).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h5v.s12.264e870c8c2b from=seed src=0 shape=29ded36c vocab=d39e6763
-/
theorem Spec.basicOpen_hom_ext {X : RingedSpace.{u}} {R : CommRingCat.{u}}
    {α β : X ⟶ Spec.sheafedSpaceObj R} (w : α.hom.base = β.hom.base)
    (h : ∀ r : R,
      let U := PrimeSpectrum.basicOpen r
      ((CommRingCat.ofHom (algebraMap R _)) ≫ α.hom.c.app (op U)) ≫
        X.presheaf.map (eqToHom (by rw [w])) =
        CommRingCat.ofHom (algebraMap _ _) ≫ β.hom.c.app (op U)) :
    α = β := by
  ext : 1
  · exact w
  · apply ((TopCat.Sheaf.pushforward _ β.hom.base).obj X.sheaf).hom_ext _
      PrimeSpectrum.isBasis_basic_opens
    intro r
    apply (StructureSheaf.to_basicOpen_epi R r).1
    simpa using! h r

set_option backward.isDefEq.respectTransparency.types false in
-- `simps!` generates some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`. -/
@[simps! toSheafedSpace presheaf]
def Spec.locallyRingedSpaceObj (R : CommRingCat.{u}) : LocallyRingedSpace where
  __ := Spec.sheafedSpaceObj R
  isLocalRing x := (stalkIso R x).toRingEquiv.isLocalRing

/--
@isnad1 id=eq.0h1v.s4.600e99228fbb from=seed src=0 shape=a8bd209c vocab=2e8d1f91
-/
lemma Spec.locallyRingedSpaceObj_sheaf (R : CommRingCat.{u}) :
    (Spec.locallyRingedSpaceObj R).sheaf = structureSheaf R := rfl

/--
@isnad1 id=eq.0h1v.s4.6dc2d6b60ae7 from=seed src=0 shape=a06427dd vocab=99d21013
-/
lemma Spec.locallyRingedSpaceObj_sheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).sheaf = structureSheaf R := rfl

/--
@isnad1 id=eq.0h4v.s9.9c2e5c881dff from=seed src=0 shape=94399629 vocab=d545c429
-/
lemma Spec.locallyRingedSpaceObj_presheaf_map (R : CommRingCat.{u}) {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

/--
@isnad1 id=eq.0h1v.s7.a49cdaf843b0 from=seed src=0 shape=b5b85a3d vocab=751468b0
-/
lemma Spec.locallyRingedSpaceObj_presheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf = (structureSheaf R).1 := rfl

/--
@isnad1 id=eq.0h4v.s9.4c93736dd169 from=seed src=0 shape=bee503be vocab=ae29c920
-/
lemma Spec.locallyRingedSpaceObj_presheaf_map' (R : Type u) [CommRing R] {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h4v.s7.8f7170809365 from=seed src=0 shape=518cf7f2 vocab=f48ddc3e
-/
@[elementwise]
theorem stalkMap_toStalk {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f.hom p) ≫ (Spec.sheafedSpaceMap f).hom.stalkMap p =
      f ≫ toStalk S p := by
  rw [← algebraMap_germ ⊤ p trivial, ← algebraMap_germ ⊤ (PrimeSpectrum.comap f.hom p) trivial,
    Category.assoc]
  erw [PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f).hom ⊤ p trivial]
  rw [Spec.sheafedSpaceMap_hom_c_app]
  erw [toOpen_comp_comap_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the isomorphisms `stalkIso`, the map `stalkMap (Spec.sheafedSpaceMap f) p` corresponds
to the induced local ring homomorphism `Localization.localRingHom`.
@isnad1 id=eq.0h4v.s11.44407941720e from=seed src=0 shape=efa5897a vocab=807cc76a
-/
@[elementwise]
theorem localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    CommRingCat.ofHom (stalkIso R (PrimeSpectrum.comap f.hom p)).symm.toRingHom ≫
      (CommRingCat.ofHom (Localization.localRingHom (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal
          f.hom rfl)) ≫
        CommRingCat.ofHom (stalkIso S p).toRingHom =
      (Spec.sheafedSpaceMap f).hom.stalkMap p :=
  (stalkIso R (PrimeSpectrum.comap f.hom p)).toCommRingCatIso.symm.eq_inv_comp.mp <|
    (stalkIso S p).toCommRingCatIso.symm.comp_inv_eq.mpr <| CommRingCat.hom_ext <|
      Localization.localRingHom_unique _ _ _ (PrimeSpectrum.comap_asIdeal _ _) fun x => by
  dsimp [-RingEquiv.symm_mk]
  simp only [AlgEquiv.commutes, RingEquiv.symm_apply_eq, AlgEquiv.coe_ringEquiv]
  exact stalkMap_toStalk_apply f p x

set_option backward.isDefEq.respectTransparency false in
/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps! toHom]
def Spec.locallyRingedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R :=
  LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f).hom fun p =>
    IsLocalHom.mk fun a ha => by
    rw [← localRingHom_comp_stalkIso] at ha
    dsimp at ha
    have : IsLocalHom (stalkIso S p) := isLocalHom_equiv _
    have : IsLocalHom (stalkIso R (p.comap f.hom)).symm := isLocalHom_equiv _
    exact ((ha.of_map (stalkIso S p)).of_map _).of_map (stalkIso R (p.comap f.hom)).symm

/--
@isnad1 id=eq.0h1v.s4.15981d2392c3 from=seed src=0 shape=b11b3d58 vocab=8565e05d
-/
@[simp]
theorem Spec.locallyRingedSpaceMap_id (R : CommRingCat.{u}) :
    Spec.locallyRingedSpaceMap (𝟙 R) = 𝟙 (Spec.locallyRingedSpaceObj R) :=
  LocallyRingedSpace.Hom.ext' <| by
    rw [Spec.locallyRingedSpaceMap_toHom, Spec.sheafedSpaceMap_id]; rfl

/--
@isnad1 id=eq.0h5v.s6.9f27f189f6ac from=seed src=0 shape=e9cd887f vocab=7400675b
-/
theorem Spec.locallyRingedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.locallyRingedSpaceMap (f ≫ g) =
      Spec.locallyRingedSpaceMap g ≫ Spec.locallyRingedSpaceMap f :=
  LocallyRingedSpace.Hom.ext' <| by
    rw [Spec.locallyRingedSpaceMap_toHom, Spec.sheafedSpaceMap_comp]; rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def Spec.toLocallyRingedSpace : CommRingCat.{u}ᵒᵖ ⥤ LocallyRingedSpace where
  obj R := Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit morphism `R ⟶ Γ(Spec R)` given by `AlgebraicGeometry.StructureSheaf.toOpen`. -/
def toSpecΓ (R : CommRingCat.{u}) : R ⟶ Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  CommRingCat.ofHom (algebraMap _ _)

/--
@isnad1 id=isiso.0h1v.s4.113244df5bee from=seed src=0 shape=0e0ab5a8 vocab=b05ec6cb
-/
instance isIso_toSpecΓ (R : CommRingCat.{u}) : IsIso (toSpecΓ R) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr algebraMap_obj_top_bijective

/--
@isnad1 id=eq.0h3v.s7.087e7fb09700 from=seed src=0 shape=39cd2a85 vocab=d3b5ef23
-/
@[reassoc]
theorem Spec_Γ_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (Spec.toLocallyRingedSpace.map f.op).op := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` failed to pick up one of the three lemmas
  ext : 2
  refine Subtype.ext <| funext fun x' => ?_; symm
  erw [comap_apply]
  apply Localization.localRingHom_to_map

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps! hom_app inv_app]
def LocallyRingedSpace.SpecΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents.{u, u, u + 1, u + 1} (fun R ↦ asIso (toSpecΓ R) :)
    fun {X Y} f => by convert! Spec_Γ_naturality (R := X) (S := Y) f

end SpecΓ

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`.
@isnad1 id=isiso.0h3v.s10.60cd381f55e0 from=seed src=0 shape=fb8cdbdb vocab=96400b7b
-/
theorem isIso_SpecMap_stakMap_localization (R : CommRingCat.{u}) (M : Submonoid R)
    (x : PrimeSpectrum (Localization M)) :
    IsIso
      ((Spec.toPresheafedSpace.map
        (CommRingCat.ofHom (algebraMap R (Localization M))).op).stalkMap x) := by
  dsimp only [Spec.toPresheafedSpace_map, Quiver.Hom.unop_op]
  rw [← localRingHom_comp_stalkIso, ConcreteCategory.isIso_iff_bijective]
  dsimp
  simp only [EquivLike.bijective_comp]
  refine (stalkIso (Localization M) x).bijective.comp ?_
  suffices
    IsIso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
        x.asIdeal).toRingEquiv.toCommRingCatIso.hom by
    rwa [ConcreteCategory.isIso_iff_bijective] at this
  infer_instance

namespace StructureSheaf

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum R)

set_option backward.isDefEq.respectTransparency.types false in
/-- For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for a `p : Spec R`.
This is shown to be the localization at `p` in `isLocalizedModule_toPushforwardStalkAlgHom`.
-/
def toPushforwardStalk : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p :=
  CommRingCat.ofHom (algebraMap _ _) ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ p trivial

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s9.f55737546a36 from=seed src=0 shape=824d2e73 vocab=ee548232
-/
@[reassoc]
theorem toPushforwardStalk_comp :
    f ≫ StructureSheaf.toPushforwardStalk f p =
      StructureSheaf.toStalk R p ≫
        (TopCat.Presheaf.stalkFunctor _ _).map (Spec.sheafedSpaceMap f).hom.c := by
  rw [StructureSheaf.toStalk, Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _

instance : Algebra R ((Spec.topMap f _* (structureSheaf S).1).stalk p) :=
  (f ≫ StructureSheaf.toPushforwardStalk f p).hom.toAlgebra

/--
@isnad1 id=eq.0h4v.s11.582c9d43aa04 from=seed src=0 shape=120c0d04 vocab=8a3e332d
-/
theorem algebraMap_pushforward_stalk :
    algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stalk p) =
      (f ≫ StructureSheaf.toPushforwardStalk f p).hom :=
  rfl

variable (R S)
variable [Algebra R S]

/--
This is the `AlgHom` version of `toPushforwardStalk`, which is the map `S ⟶ (f∗ 𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
@[simps!]
def toPushforwardStalkAlgHom :
    S →ₐ[R] (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).stalk p :=
  { (StructureSheaf.toPushforwardStalk (CommRingCat.ofHom (algebraMap R S)) p).hom with
    commutes' := fun _ => rfl }

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=ex.0h4v.s12.cfc90f80f247 from=seed src=0 shape=843c552d vocab=f90af4dc
-/
theorem isLocalizedModule_toPushforwardStalkAlgHom_aux (y) :
    ∃ x : S × p.asIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1 := by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.exists_germ_eq _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p ∈ PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r ≤ U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U from hp) U.2
  change PrimeSpectrum.basicOpen r ≤ U at hrU
  replace e :=
    ((Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).germ_res_apply
      (homOfLE hrU) p hpr _).trans e
  set s' := (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).map
      (homOfLE hrU).op s with h
  replace e : ((Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).obj).germ _
      p hpr) s' = y := by
    rw [h]; exact e
  clear_value s'; clear! U
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ :=
    @IsLocalization.surj _ _ _ _ _ _
      (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) s'
  refine ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def, algebraMap_pushforward_stalk, toPushforwardStalk,
    CommRingCat.comp_apply, CommRingCat.comp_apply]
  iterate 2
    erw [← (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).germ_res_apply
      (homOfLE le_top) p hpr]
  rw [← e]
  let f := TopCat.Presheaf.germ (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _*
      (structureSheaf S).obj) _ p hpr
  rw [← map_mul, mul_comm]
  dsimp only [Subtype.coe_mk] at hsn
  rw [← map_pow (algebraMap R S)] at hsn
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=islocali.0h3v.s12.432b93d09020 from=seed src=0 shape=70e23fba vocab=2b095118
-/
instance isLocalizedModule_toPushforwardStalkAlgHom :
    IsLocalizedModule p.asIdeal.primeCompl (toPushforwardStalkAlgHom R S p).toLinearMap := by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx; rw [algebraMap_pushforward_stalk, toPushforwardStalk_comp]
    change IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap ↑R ↑S))).hom.c _)
    exact (IsLocalization.map_units ((structureSheaf R).presheaf.stalk p) ⟨x, hx⟩).map _
  · apply isLocalizedModule_toPushforwardStalkAlgHom_aux
  · intro x hx
    rw [toPushforwardStalkAlgHom_apply,
      ← (toPushforwardStalk (CommRingCat.ofHom (algebraMap ↑R ↑S)) p).hom.map_zero,
      toPushforwardStalk] at hx
    rw [CommRingCat.comp_apply, map_zero] at hx
    obtain ⟨U, hpU, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq (C := CommRingCat) _ _ _ _ _ _ hx
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U.1 from hpU)
        U.2
    apply_fun (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).map
        (homOfLE hrU).op at e
    have : algebraMap S ((structureSheaf S).presheaf.obj _) x = 0 := e
    have :=
      (@IsLocalization.mk'_one _ _ _ _ _ _
            (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) x).trans
        this
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp this
    refine ⟨⟨r, hpr⟩ ^ n, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, SubmonoidClass.coe_pow, map_pow]
    exact e

end StructureSheaf

end AlgebraicGeometry
