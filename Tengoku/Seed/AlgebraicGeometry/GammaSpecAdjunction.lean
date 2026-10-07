/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Restrict
public import Tengoku.Seed.CategoryTheory.Adjunction.Limits
public import Tengoku.Seed.CategoryTheory.Adjunction.Opposites
public import Tengoku.Seed.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `ΓSpec.adjunction : Γ ⊣ Spec` by defining the unit (`toΓSpec`,
in multiple steps in this file) and counit (done in `Spec.lean`) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`
extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `AlgebraicGeometry.identityToΓSpec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `AlgebraicGeometry.ΓSpec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open TopCat.Presheaf

open TopCat.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h3v.s11.397597956fd0 from=seed src=0 shape=e3d59bf4 vocab=77db885f
-/
theorem notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r) := by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

set_option backward.isDefEq.respectTransparency false in
/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets).
@isnad1 id=eq.0h2v.s11.0067df1c9abd from=seed src=0 shape=e7ab19ed vocab=d0a7bfef
-/
theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' basicOpen r = SetLike.coe (X.toRingedSpace.basicOpen r) := by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

/-- `toΓSpecFun` is continuous.
@isnad1 id=continuo.0h1v.s6.53db526e4ca6 from=seed src=0 shape=7ba188b9 vocab=e3c45686
-/
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) :=
  TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)

/-- The preimage is the basic open in `X` defined by the same element `r`.
@isnad1 id=eq.0h2v.s11.92a6afd80a14 from=seed src=0 shape=dd070318 vocab=9b589692
-/
theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbrev toToΓSpecMapBasicOpen :
    X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

set_option backward.isDefEq.respectTransparency false in
/-- `r` is a unit as a section on the basic open defined by `r`.
@isnad1 id=isunit.0h2v.s11.25ebabb79694 from=seed src=0 shape=63a7029d vocab=98423c71
-/
theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert!
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr

/-- Define the sheaf hom on individual basic opens for the unit. -/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
  CommRingCat.ofHom <|
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).obj.obj (op (basicOpen r)))
      r
      (isUnit_res_toΓSpecMapBasicOpen _ r)

set_option backward.isDefEq.respectTransparency false in
/-- Characterization of the sheaf hom on basic opens,
direction ← (next lemma) is used at various places, but → is not used in this file.
@isnad1 id=iff.0h3v.s13.7c699df128b4 from=seed src=0 shape=cd0f3a46 vocab=88341bd8
-/
theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
        X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ f = X.toToΓSpecMapBasicOpen r ↔
      f = X.toΓSpecCApp r := by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Submonoid.powers r) h
  apply congr_arg

/--
@isnad1 id=eq.0h2v.s13.f062470129da from=seed src=0 shape=0a08e46d vocab=fe4fbd53
-/
theorem toΓSpecCApp_spec :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf hom on all basic opens, commuting with restrictions. -/
@[simps app]
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((TopCat.Sheaf.pushforward _ X.toΓSpecBase).obj X.𝒪).1 where
  app r := X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    simp only [← Category.assoc]
    rw [show algebraMap (Γ.obj (op X)) ((structureSheaf (Γ.obj (op X))).obj.obj _) = algebraMap _
      ((structureSheafInType (Γ.obj (op X)) (Γ.obj (op X))).obj.obj _) from rfl,
      X.toΓSpecCApp_spec r.unop]
    convert! X.toΓSpecCApp_spec s.unop
    symm
    apply X.presheaf.map_comp

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps! -isSimp]
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) :=
  InducedCategory.homMk
    { base := X.toΓSpecBase
      c :=
        TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
          X.toΓSpecCBasicOpens }

/--
@isnad1 id=eq.0h2v.s11.78b9c650ee38 from=seed src=0 shape=c39a1b5f vocab=b8497cb9
-/
theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) = X.toΓSpecCApp r := by
  apply TopCat.Sheaf.extend_hom_app _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s13.5fd17adb1866 from=seed src=0 shape=43d4c006 vocab=fc4c9171
-/
@[reassoc] theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫
        X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r

set_option backward.isDefEq.respectTransparency false in
/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
stalks (in `Spec Γ(X)` and in `X`).
@isnad1 id=eq.0h2v.s9.42353046d14a from=seed src=0 shape=926fb629 vocab=f25dfa66
-/
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ _ ≫ X.toΓSpecSheafedSpace.hom.stalkMap x = X.presheaf.Γgerm x := by
  rw [PresheafedSpace.Hom.stalkMap,
    ← algebraMap_germ (basicOpen (1 : Γ.obj (op X))) _ (by rw [basicOpen_one]; trivial),
    ← Category.assoc, Category.assoc (CommRingCat.ofHom _), stalkFunctor_map_germ, ← Category.assoc,
    X.toΓSpecSheafedSpace_app_eq, X.toΓSpecCApp_spec, Γgerm,
    ← dsimp% stalkPushforward_germ _ _ X.presheaf ⊤]
  congr 1
  exact (X.toΓSpecBase _* X.presheaf).germ_res le_top.hom _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps! base]
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) :=
  LocallyRingedSpace.homMk (X.toΓSpecSheafedSpace) (fun x ↦ by
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdeal.primeCompl t
    dsimp at he
    set t' := _
    change t * t' = _ at he
    apply isUnit_of_mul_isUnit_left (y := t')
    rw [he]
    refine IsLocalization.map_units S (⟨r, ?_⟩ : p.asIdeal.primeCompl)
    apply (notMem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← toStalk_stalkMap_toΓSpec, CommRingCat.comp_apply]
    erw [← he]
    rw [map_mul]
    exact ht.mul <| (IsLocalization.map_units (R := Γ.obj (op X)) S s).map _)

set_option backward.isDefEq.respectTransparency false in
/-- On a locally ringed space `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `toΓSpec` agrees with the associated zero locus on `X`.
@isnad1 id=eq.0h2v.s10.28974b2e6514 from=seed src=0 shape=4603d083 vocab=3d51a06e
-/
lemma toΓSpec_preimage_zeroLocus_eq {X : LocallyRingedSpace.{u}}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpec.base ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i ∈ s) :
      (SetLike.coe (X.toRingedSpace.basicOpen i))ᶜ =
        X.toΓSpec.base ⁻¹' ((PrimeSpectrum.basicOpen i).carrier)ᶜ := by
    symm
    rw [Set.preimage_compl, Opens.carrier_eq_coe]
    erw [X.toΓSpec_preimage_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  simp_rw [← Set.preimage_iInter₂, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.2h4v.s12.2fea3ffd15f0 from=seed src=0 shape=cb87221e vocab=ed6b0138
-/
theorem comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.base ≫ (Spec.locallyRingedSpaceMap f).base = β.base)
    (h :
      ∀ r : R,
        f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.base).obj (basicOpen r) ⟶ _).op =
          CommRingCat.ofHom (algebraMap _ _) ≫ β.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  refine LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (Spec.basicOpen_hom_ext w ?_)
  intro r U
  erw [SheafedSpace.comp_hom_c_app, toOpen_comp_comap_assoc]
  dsimp
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

set_option backward.isDefEq.respectTransparency.types false in
/-- `toSpecΓ _` is an isomorphism so these are mutually two-sided inverses.
@isnad1 id=eq.0h1v.s11.be9b79cd0537 from=seed src=0 shape=0e1b3aca vocab=64595a58
-/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _ := by
  unfold toSpecΓ
  have := X.toΓSpecSheafedSpace_app_spec 1
  unfold toToΓSpecMapBasicOpen toΓSpecMapBasicOpen at this
  rw! [basicOpen_one] at this
  convert! this
  exact (X.presheaf.map_id ..).symm

end LocallyRingedSpace

set_option backward.isDefEq.respectTransparency false in
/-- The unit as a natural transformation. -/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp
      change PrimeSpectrum.comap (f.c.app (op ⊤)).hom (X.toΓSpecFun x) = Y.toΓSpecFun (f.base x)
      dsimp [toΓSpecFun]
      rw [← IsLocalRing.comap_closedPoint (f.stalkMap x).hom, ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
        ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 2
      exact (PresheafedSpace.stalkMap_germ f.1 ⊤ x trivial).symm
    · intro r
      rw [LocallyRingedSpace.comp_c_app, ← Category.assoc]
      erw [Y.toΓSpecSheafedSpace_app_spec, f.c.naturality]
      rfl

namespace ΓSpec

/--
@isnad1 id=eq.0h1v.s12.c808de9a7bb0 from=seed src=0 shape=d3f53ebb vocab=c0daf7c5
-/
theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `SpecΓIdentity` is iso so these are mutually two-sided inverses.
@isnad1 id=eq.0h1v.s8.700e3d69dd7d from=seed src=0 shape=adc85c6e vocab=77f449d9
-/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ := by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps]
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  unit := identityToΓSpec
  counit := (NatIso.op SpecΓIdentity).inv
  left_triangle_components X := by
    simp only [Functor.id_obj, Γ_obj, Functor.rightOp_map, Γ_map,
      Quiver.Hom.unop_op, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact congr_arg Quiver.Hom.op (left_triangle X)
  right_triangle_components R := by
    simp only [Functor.id_obj, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact right_triangle R.unop


set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h1v.s14.f952cc2c3981 from=seed src=0 shape=0af3b079 vocab=4fae3114
-/
lemma toSpecΓ_unop (R : CommRingCatᵒᵖ) :
    AlgebraicGeometry.toSpecΓ (Opposite.unop R) = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `locallyRingedSpaceAdjunction_counit_app'`.
@isnad1 id=eq.0h1v.s14.e52ead398ce9 from=seed src=0 shape=64ea79d8 vocab=e26d5b3d
-/
@[simp]
lemma toSpecΓ_of (R : Type u) [CommRing R] :
    AlgebraicGeometry.toSpecΓ (CommRingCat.of R) = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h1v.s14.5ed3460462e1 from=seed src=0 shape=f3c76650 vocab=649a9abf
-/
lemma locallyRingedSpaceAdjunction_counit_app (R : CommRingCatᵒᵖ) :
    locallyRingedSpaceAdjunction.counit.app R =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h1v.s15.720c6f0139d3 from=seed src=0 shape=524c7f93 vocab=20802cac
-/
lemma locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R) =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h1v.s14.7f96ed654aa6 from=seed src=0 shape=73992eab vocab=a69048a6
-/
lemma unop_locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    (locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R)).unop =
      (CommRingCat.ofHom (algebraMap _ _)) := rfl

/--
@isnad1 id=eq.0h3v.s8.39ff8c053055 from=seed src=0 shape=d33cee37 vocab=5309e288
-/
lemma locallyRingedSpaceAdjunction_homEquiv_apply
    {X : LocallyRingedSpace} {R : CommRingCatᵒᵖ}
    (f : Γ.rightOp.obj X ⟶ R) :
    locallyRingedSpaceAdjunction.homEquiv X R f =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f.unop := rfl

/--
@isnad1 id=eq.0h3v.s8.6cbd210956a0 from=seed src=0 shape=e93ba615 vocab=af741ec7
-/
lemma locallyRingedSpaceAdjunction_homEquiv_apply'
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : CommRingCat.of R ⟶ Γ.obj <| op X) :
    locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) (op f) =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s14.ff5dbf5d0a41 from=seed src=0 shape=f19599c2 vocab=a3d92ea0
-/
lemma toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : Γ.rightOp.obj X ⟶ op (CommRingCat.of R)) (U) :
    CommRingCat.ofHom (algebraMap R _) ≫
      (locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) f).c.app U =
    f.unop ≫ X.presheaf.map (homOfLE le_top).op := by
  dsimp
  rw [← StructureSheaf.algebraMap_self_map _ U _ (homOfLE le_top).op, Category.assoc,
    NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op,
    ← unop_locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop, ← Category.assoc, ← unop_comp]
  erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  unit :=
  { app := fun X ↦ ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun _ _ f ↦
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
  left_triangle_components Y :=
    locallyRingedSpaceAdjunction.left_triangle_components Y.toLocallyRingedSpace
  right_triangle_components R :=
    Scheme.Hom.ext' <| locallyRingedSpaceAdjunction.right_triangle_components R

/-- Given `f, g : X ⟶ Spec(R)`, if the two induced maps `R ⟶ Γ(X)` are equal, then `f = g`. -/
lemma _root_.AlgebraicGeometry.ext_to_Spec {X : Scheme} {R : Type*} [CommRing R]
    {f g : X ⟶ Spec (.of R)}
    (h : (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map f.op =
      (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map g.op) :
    f = g :=
  (ΓSpec.adjunction.homEquiv X (.op <| .of R)).symm.injective <| Opposite.unop_injective h

/--
@isnad1 id=eq.0h3v.s9.1c6b96a5082b from=seed src=0 shape=39010620 vocab=16ca9178
-/
theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = ⟨locallyRingedSpaceAdjunction.homEquiv X.1 R f⟩ := rfl

/--
@isnad1 id=eq.0h3v.s9.689c590f7fba from=seed src=0 shape=da4e9f9f vocab=45794c38
-/
theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.Spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f =
      (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f.toLRSHom := rfl

/--
@isnad1 id=eq.0h1v.s7.1cc7149fcedc from=seed src=0 shape=e3843f56 vocab=d029a6af
-/
theorem adjunction_counit_app' {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := rfl

/--
@isnad1 id=eq.0h1v.s9.8500293448af from=seed src=0 shape=43ceb9c6 vocab=5de81ac2
-/
@[simp]
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = (Scheme.ΓSpecIso (unop R)).inv.op := rfl

/-- The canonical map `X ⟶ Spec Γ(X, ⊤)`. This is the unit of the `Γ-Spec` adjunction. -/
def _root_.AlgebraicGeometry.Scheme.toSpecΓ (X : Scheme.{u}) : X ⟶ Spec Γ(X, ⊤) :=
  ΓSpec.adjunction.unit.app X

/--
@isnad1 id=eq.0h1v.s6.333bcda9f50d from=seed src=0 shape=4c211e07 vocab=316efe0c
-/
@[simp]
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.unit.app X = X.toSpecΓ := rfl

/--
@isnad1 id=isiso.0h0v.s6.a27e632888af from=seed src=0 shape=72705500 vocab=d94c1251
-/
instance isIso_locallyRingedSpaceAdjunction_counit :
    IsIso.{u + 1, u + 1} locallyRingedSpaceAdjunction.counit :=
  (NatIso.op SpecΓIdentity).isIso_inv

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isiso.0h0v.s6.9a167cd2747b from=seed src=0 shape=72705500 vocab=d48e76ba
-/
instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply +allowSynthFailures NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

end ΓSpec

/--
@isnad1 id=eq.0h2v.s12.0ee3f5bc6642 from=seed src=0 shape=00afb218 vocab=4a5f0843
-/
theorem Scheme.toSpecΓ_apply (X : Scheme.{u}) (x) :
    Scheme.toSpecΓ X x = Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _) := rfl

/--
@isnad1 id=eq.0h3v.s10.7ca565a166bc from=seed src=0 shape=8dcb64fe vocab=f93c4c16
-/
@[reassoc]
theorem Scheme.toSpecΓ_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map f.appTop :=
  ΓSpec.adjunction.unit.naturality f

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h1v.s13.d59f201c847a from=seed src=0 shape=b3ee86ce vocab=43b03f14
-/
@[simp]
theorem Scheme.toSpecΓ_appTop (X : Scheme.{u}) :
    X.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff, this, ← op_inv, IsIso.Iso.inv_inv]

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h1v.s9.4631acbde3ce from=seed src=0 shape=1463d2d6 vocab=e0c60c0a
-/
@[simp]
theorem SpecMap_ΓSpecIso_hom (R : CommRingCat.{u}) :
    Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ := by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

/--
@isnad1 id=eq.0h1v.s10.c6ca8b7e22bf from=seed src=0 shape=732a035f vocab=52f49224
-/
@[reassoc (attr := simp)]
theorem SpecMap_ΓSpecIso_inv_toSpecΓ (R : CommRingCat.{u}) :
    Spec.map (Scheme.ΓSpecIso R).inv ≫ (Spec R).toSpecΓ = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

/--
@isnad1 id=eq.0h1v.s9.b1a4c64c580c from=seed src=0 shape=123669d9 vocab=52f49224
-/
@[reassoc (attr := simp)]
theorem toSpecΓ_SpecMap_ΓSpecIso_inv (R : CommRingCat.{u}) :
    (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

/--
@isnad1 id=eq.0h2v.s11.0bb0e7fe9661 from=seed src=0 shape=ba2b6463 vocab=5efc9966
-/
lemma Scheme.toSpecΓ_preimage_basicOpen (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen r := by
  rw [← basicOpen_eq_of_affine, Scheme.preimage_basicOpen, ← Scheme.Hom.appTop]
  congr
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s10.4b9572822bb2 from=seed src=0 shape=17c19732 vocab=67ebc39b
-/
lemma ΓSpecIso_inv_ΓSpec_adjunction_homEquiv {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = φ := by
  simp only [Adjunction.homEquiv_apply, Scheme.Spec_map, Opens.map_top, Scheme.Hom.comp_app]
  simp

/--
@isnad1 id=eq.0h3v.s11.f1f7ae6c6573 from=seed src=0 shape=2885f347 vocab=0bd6d274
-/
lemma ΓSpec_adjunction_homEquiv_eq {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [← Iso.inv_comp_eq, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h2v.s15.d004efa97550 from=seed src=0 shape=129b21c0 vocab=934c0b3c
-/
theorem ΓSpecIso_obj_hom {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).hom = (Spec.map U.topIso.inv).appTop ≫
      U.toScheme.toSpecΓ.appTop ≫ U.topIso.hom := by simp

/-! Immediate consequences of the adjunction. -/

/-- The functor `Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace`
is fully faithful. -/
def Spec.fullyFaithfulToLocallyRingedSpace : Spec.toLocallyRingedSpace.FullyFaithful :=
  ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor. -/
instance : Spec.toLocallyRingedSpace.Full :=
  Spec.fullyFaithfulToLocallyRingedSpace.full

/-- Spec is a faithful functor. -/
instance : Spec.toLocallyRingedSpace.Faithful :=
  Spec.fullyFaithfulToLocallyRingedSpace.faithful

/-- The functor `Spec : CommRingCatᵒᵖ ⥤ Scheme` is fully faithful. -/
def Spec.fullyFaithful : Scheme.Spec.FullyFaithful :=
  ΓSpec.adjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor.
@isnad1 id=full.0h0v.s3.f64af454b96e from=seed src=0 shape=836e6cbb vocab=891e9391
-/
instance Spec.full : Scheme.Spec.Full :=
  Spec.fullyFaithful.full

/-- Spec is a faithful functor.
@isnad1 id=faithful.0h0v.s3.f95c79d09114 from=seed src=0 shape=836e6cbb vocab=abcff02a
-/
instance Spec.faithful : Scheme.Spec.Faithful :=
  Spec.fullyFaithful.faithful

section

variable {R S : CommRingCat.{u}} {φ ψ : R ⟶ S} (f : Spec S ⟶ Spec R)

/--
@isnad1 id=iff.0h4v.s5.13d2a86e1b23 from=seed src=0 shape=7c69fd33 vocab=18aad7e1
-/
lemma Spec.map_inj : Spec.map φ = Spec.map ψ ↔ φ = ψ := by
  rw [iff_comm, ← Quiver.Hom.op_inj.eq_iff, ← Scheme.Spec.map_injective.eq_iff]
  rfl

/--
@isnad1 id=injectiv.0h2v.s4.5c5daba7aa93 from=seed src=0 shape=ede2e0b2 vocab=cf1d2b52
-/
lemma Spec.map_injective {R S : CommRingCat} : Function.Injective (Spec.map : (R ⟶ S) → _) :=
  fun _ _ ↦ Spec.map_inj.mp

/--
@isnad1 id=iff.0h2v.s5.b16faea53072 from=seed src=0 shape=02961c18 vocab=e2c5bc5a
-/
@[simp]
lemma Spec.map_eq_id {R : CommRingCat} {ϕ : R ⟶ R} : Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R := by
  simp [← map_inj]

/-- The preimage under Spec. -/
def Spec.preimage : R ⟶ S := (Scheme.Spec.preimage f).unop

/--
@isnad1 id=eq.0h3v.s5.608caa792586 from=seed src=0 shape=bfc2d328 vocab=ebfb951f
-/
@[simp] lemma Spec.map_preimage : Spec.map (Spec.preimage f) = f := Scheme.Spec.map_preimage f

/--
@isnad1 id=eq.0h3v.s6.c3f805007aaf from=seed src=0 shape=810e6cd3 vocab=213f3f86
-/
@[simp] lemma Spec.map_preimage_unop (f : Spec R ⟶ Spec S) :
    Spec.map (Spec.fullyFaithful.preimage f).unop = f := Spec.fullyFaithful.map_preimage _

variable (φ) in
/--
@isnad1 id=eq.0h3v.s5.3d04307e33be from=seed src=0 shape=95269547 vocab=3577b9bb
-/
@[simp] lemma Spec.preimage_map : Spec.preimage (Spec.map φ) = φ :=
  Spec.map_injective (Spec.map_preimage (Spec.map φ))

/-- Useful for replacing `f` by `Spec.map φ` everywhere in proofs.
@isnad1 id=surjecti.0h2v.s4.4d923e9a3f5e from=seed src=0 shape=ede2e0b2 vocab=fa932905
-/
lemma Spec.map_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) → _) := by
  intro f
  use Spec.preimage f
  simp

/-- Spec is fully faithful -/
@[simps]
def Spec.homEquiv {R S : CommRingCat} : (Spec S ⟶ Spec R) ≃ (R ⟶ S) where
  toFun := Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

/--
@isnad1 id=eq.0h1v.s4.9c9d5773b854 from=seed src=0 shape=062b88d2 vocab=8d529304
-/
@[simp]
lemma Spec.preimage_id {R : CommRingCat} : Spec.preimage (𝟙 (Spec R)) = 𝟙 R :=
  Spec.map_injective (by simp)

/--
@isnad1 id=eq.0h5v.s6.38aeae34f344 from=seed src=0 shape=225e8afe vocab=e3eeb5e2
-/
@[simp, reassoc]
lemma Spec.preimage_comp {R S T : CommRingCat} (f : Spec R ⟶ Spec S) (g : Spec S ⟶ Spec T) :
    Spec.preimage (f ≫ g) = Spec.preimage g ≫ Spec.preimage f :=
  Spec.map_injective (by simp)

end

instance : Reflective Spec.toLocallyRingedSpace where
  L := Γ.rightOp
  adj := ΓSpec.locallyRingedSpaceAdjunction

instance Spec.reflective : Reflective Scheme.Spec where
  L := Scheme.Γ.rightOp
  adj := ΓSpec.adjunction

instance : LocallyRingedSpace.Γ.IsRightAdjoint :=
  ΓSpec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint

instance : Scheme.Γ.IsRightAdjoint := ΓSpec.adjunction.rightOp.isRightAdjoint

end AlgebraicGeometry
