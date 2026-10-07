/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.AffineScheme
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Stalks of a Scheme

## Main definitions and results

- `AlgebraicGeometry.Scheme.fromSpecStalk`: The canonical morphism `Spec 𝒪_{X, x} ⟶ X`.
- `AlgebraicGeometry.Scheme.range_fromSpecStalk`: The range of the map `Spec 𝒪_{X, x} ⟶ X` is
  exactly the `y`s that specialize to `x`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing`:
  Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
  `(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

section fromSpecStalk

/--
A morphism from `Spec(O_x)` to `X`, which is defined with the help of an affine open
neighborhood `U` of `x`.
-/
noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

/--
The morphism from `Spec(O_x)` to `X` given by `IsAffineOpen.fromSpec` does not depend on the affine
open neighborhood of `x` we choose.
@isnad1 id=eq.4h4v.s7.c8abc9a66907 from=seed src=0 shape=0404f0db vocab=3021d9d7
-/
theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op, ← Spec.map_comp_assoc,
      TopCat.Presheaf.germ_res]
  · delta fromSpecStalk
    rw [← hV.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_right).op, ← Spec.map_comp_assoc,
      TopCat.Presheaf.germ_res]

/--
If `x` is a point of `X`, this is the canonical morphism from `Spec(O_x)` to `X`.
-/
noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).fromSpecStalk
    (X.affineCover.covers x)

@[simps over] noncomputable
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).Over X := ⟨X.fromSpecStalk x⟩

noncomputable
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).CanonicallyOver X where

/--
@isnad1 id=eq.2h3v.s6.f00b6c0f913b from=seed src=0 shape=893a5fb8 vocab=77d4e89b
-/
@[simp]
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := fromSpecStalk_eq ..

/--
@isnad1 id=ispreimm.2h3v.s7.4e953fdc9dfd from=seed src=0 shape=5ffd1422 vocab=3599acf3
-/
instance IsAffineOpen.fromSpecStalk_isPreimmersion {X : Scheme.{u}} {U : Opens X}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) : IsPreimmersion (hU.fromSpecStalk hx) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply IsPreimmersion.comp

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.2h3v.s9.00c33d237c6a from=seed src=0 shape=181d4d61 vocab=d028c7ac
-/
lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU (closedPoint (X.presheaf.stalk x)) = x := by
  rw [IsAffineOpen.fromSpecStalk, Scheme.Hom.comp_apply]
  rw [← hU.primeIdealOf_eq_map_closedPoint ⟨x, hxU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩]

namespace Scheme

/--
@isnad1 id=eq.0h2v.s8.c1372bbdbad0 from=seed src=0 shape=7928de7f vocab=aec1a4bf
-/
@[simp]
lemma fromSpecStalk_closedPoint {x : X} :
    X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x :=
  IsAffineOpen.fromSpecStalk_closedPoint _ _

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s12.37c64fdac57c from=seed src=0 shape=aa73559e vocab=d01d3ee0
-/
lemma fromSpecStalk_app {x : X} (hxU : x ∈ U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ U x hxU ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU U.2
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk, Scheme.Hom.comp_app,
    hV.fromSpec_app_of_le _ hVU, ← X.presheaf.germ_res (homOfLE hVU) x hxV]
  simp [Category.assoc, ← ΓSpecIso_inv_naturality_assoc]

/--
@isnad1 id=eq.0h2v.s13.2e03a46d6f46 from=seed src=0 shape=45945dd1 vocab=1f08a926
-/
lemma fromSpecStalk_appTop {x : X} :
    (X.fromSpecStalk x).appTop =
      X.presheaf.germ ⊤ x trivial ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op :=
  fromSpecStalk_app ..

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h3v.s7.06b61b524d68 from=seed src=0 shape=6ea3b7a0 vocab=b6f67d77
-/
@[reassoc (attr := simp)]
lemma SpecMap_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x ∈ U := h.mem_open U.2 hyU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU, ← hU.fromSpecStalk_eq_fromSpecStalk hxU,
    IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp,
    TopCat.Presheaf.germ_stalkSpecializes]

instance {x y : X} (h : x ⤳ y) : (Spec.map (X.presheaf.stalkSpecializes h)).IsOver X where

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h4v.s9.8ba152f45fff from=seed src=0 shape=59b95512 vocab=5a20f361
-/
@[reassoc (attr := simp)]
lemma SpecMap_stalkMap_fromSpecStalk {x} :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, ← hV.fromSpecStalk_eq_fromSpecStalk hxV,
    IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc, Scheme.Hom.germ_stalkMap f _ x hxU,
    IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc, ← X.presheaf.germ_res (homOfLE hVU) x hxV,
    Spec.map_comp_assoc, Category.assoc, ← Spec.map_comp_assoc (f.app _),
      Hom.app_eq_appLE, Hom.appLE_map, IsAffineOpen.SpecMap_appLE_fromSpec]

instance [X.Over Y] {x} : Spec.map ((X ↘ Y).stalkMap x) |>.IsOver Y where

/--
@isnad1 id=eq.0h2v.s8.496d2d6415b8 from=seed src=0 shape=31c90cbc vocab=8e8a52fa
-/
@[stacks 01J7]
lemma range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x) = { y | y ⤳ x } := by
  ext y
  constructor
  · rintro ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq fromSpecStalk_closedPoint)
  · rintro (hy : y ⤳ x)
    have := fromSpecStalk_closedPoint (x := y)
    rw [← SpecMap_stalkSpecializes_fromSpecStalk hy] at this
    exact ⟨_, this⟩

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map `Spec 𝒪_{X, x} ⟶ U` given `x ∈ U ⊆ X`. -/
noncomputable
def Opens.fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ U :=
  Spec.map (inv (U.ι.stalkMap ⟨x, hxU⟩)) ≫ U.toScheme.fromSpecStalk ⟨x, hxU⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h3v.s7.1fb331970f87 from=seed src=0 shape=5deb4964 vocab=26dbcb54
-/
@[reassoc (attr := simp)]
lemma Opens.fromSpecStalkOfMem_ι {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x := by
  simp only [Opens.fromSpecStalkOfMem, Spec.map_inv, Category.assoc, IsIso.inv_comp_eq]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk U.ι (x := ⟨x, hxU⟩)).symm

instance {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    (U.fromSpecStalkOfMem x hxU).IsOver X where

/--
@isnad1 id=eq.0h2v.s10.540c8367c6b8 from=seed src=0 shape=bc168fcf vocab=f699a1d8
-/
@[reassoc]
lemma fromSpecStalk_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecStalk x ≫ X.toSpecΓ = Spec.map (X.presheaf.germ ⊤ x trivial) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    Scheme.fromSpecStalk_appTop]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s9.0e7ef9951660 from=seed src=0 shape=a165c99d vocab=a937d4d8
-/
@[reassoc (attr := simp)]
lemma Opens.fromSpecStalkOfMem_toSpecΓ {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ = Spec.map (X.presheaf.germ U x hxU) := by
  rw [fromSpecStalkOfMem, Opens.toSpecΓ, Category.assoc, fromSpecStalk_toSpecΓ_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq, Iso.inv_comp_eq]
  erw [Hom.germ_stalkMap U.ι U ⟨x, hxU⟩]
  rw [Opens.ι_app, Opens.topIso_hom, ← Functor.map_comp_assoc]
  exact (U.toScheme.presheaf.germ_res (homOfLE le_top) ⟨x, hxU⟩ (U := U.ι ⁻¹ᵁ U) hxU).symm

end Scheme

section Spec

variable (R : CommRingCat) (x)

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.558327dbb3a6 from=seed src=0 shape=a3cd9842 vocab=a4f4c997
-/
lemma Spec.fromSpecStalk_eq :
    (Spec R).fromSpecStalk x =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) := by
  rw [← (isAffineOpen_top (Spec R)).fromSpecStalk_eq_fromSpecStalk (x := x) trivial,
    IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]

-- This is not a simp lemma to respect the abstraction boundaries
/-- A variant of `Spec.fromSpecStalk_eq` that breaks abstraction boundaries.
@isnad1 id=eq.0h2v.s6.1903fdc374fb from=seed src=0 shape=e8c002f7 vocab=d9e21515
-/
lemma Spec.fromSpecStalk_eq' : (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _) :=
  Spec.fromSpecStalk_eq _ _

/--
@isnad1 id=eq.0h2v.s10.558327dbb3a6 from=seed src=0 shape=a3cd9842 vocab=a4f4c997
-/
@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk := Spec.fromSpecStalk_eq
/--
@isnad1 id=eq.0h2v.s6.1903fdc374fb from=seed src=0 shape=e8c002f7 vocab=d9e21515
-/
@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk' := Spec.fromSpecStalk_eq'

end Spec

end fromSpecStalk

variable (R : CommRingCat.{u}) [IsLocalRing R]

section stalkClosedPointIso

/-- For a local ring `(R, 𝔪)`,
this is the isomorphism between the stalk of `Spec R` at `𝔪` and `R`. -/
noncomputable
def stalkClosedPointIso :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R :=
  Spec.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ ↦ not_not.mp).toRingEquiv.toCommRingCatIso.symm

/--
@isnad1 id=eq.0h1v.s6.b016eb539553 from=seed src=0 shape=5de763f2 vocab=5c9b8358
-/
lemma stalkClosedPointIso_inv :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ := by
  ext x
  exact (StructureSheaf.stalkIso _ _).commutes _

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h1v.s10.6360070856b1 from=seed src=0 shape=5e7a68f4 vocab=4c2ba195
-/
lemma ΓSpecIso_hom_stalkClosedPointIso_inv :
    (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv =
      (Spec R).presheaf.germ ⊤ (closedPoint _) trivial := by
  rw [stalkClosedPointIso_inv, ← Iso.eq_inv_comp]
  rfl

/--
@isnad1 id=eq.0h1v.s10.ac90ea525479 from=seed src=0 shape=3cf53d26 vocab=5981558e
-/
@[reassoc (attr := simp)]
lemma germ_stalkClosedPointIso_hom :
    (Spec R).presheaf.germ ⊤ (closedPoint _) trivial ≫ (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom := by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h1v.s7.7ebfcbbcf7f2 from=seed src=0 shape=c8991691 vocab=bb52e8b1
-/
lemma Spec_stalkClosedPointIso :
    Spec.map (stalkClosedPointIso R).inv = (Spec R).fromSpecStalk (closedPoint R) := by
  rw [stalkClosedPointIso_inv, Spec.fromSpecStalk_eq']

end stalkClosedPointIso

section stalkClosedPointTo

variable {R} (f : Spec R ⟶ X)

namespace Scheme

/--
Given a local ring `(R, 𝔪)` and a morphism `f : Spec R ⟶ X`,
they induce a (local) ring homomorphism `φ : 𝒪_{X, f 𝔪} ⟶ R`.

This is inverse to `φ ↦ Spec.map φ ≫ X.fromSpecStalk (f 𝔪)`. See `SpecToEquivOfLocalRing`.
-/
noncomputable
def stalkClosedPointTo :
    X.presheaf.stalk (f (closedPoint R)) ⟶ R :=
  f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=islocalh.0h3v.s11.a54d24819ede from=seed src=0 shape=c9c2349a vocab=a95e6134
-/
instance isLocalHom_stalkClosedPointTo :
    IsLocalHom (stalkClosedPointTo f).hom :=
  inferInstanceAs <| IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom

/-- Copy of `isLocalHom_stalkClosedPointTo` which unbundles the comm ring.

Useful for use in combination with `CommRingCat.of K` for a field `K`.
@isnad1 id=islocalh.0h3v.s11.6857ffa2dd5b from=seed src=0 shape=c86b0ff5 vocab=5d639de1
-/
instance isLocalHom_stalkClosedPointTo' {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ X) :
    IsLocalHom (stalkClosedPointTo f).hom :=
  isLocalHom_stalkClosedPointTo f

/--
@isnad1 id=eq.1h4v.s9.af9c2e460fea from=seed src=0 shape=7e20a567 vocab=51d97053
-/
lemma preimage_eq_top_of_closedPoint_mem
    {U : Opens X} (hU : f (closedPoint R) ∈ U) : f ⁻¹ᵁ U = ⊤ :=
  IsLocalRing.closed_point_mem_iff.mp hU

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h5v.s10.29ffb1c175fa from=seed src=0 shape=556b3501 vocab=29a5398a
-/
lemma stalkClosedPointTo_comp (g : X ⟶ Y) :
    stalkClosedPointTo (f ≫ g) = g.stalkMap _ ≫ stalkClosedPointTo f := by
  rw [stalkClosedPointTo, Scheme.Hom.stalkMap_comp]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s11.002ff025b7e4 from=seed src=0 shape=15e93e42 vocab=0fdb5f4e
-/
lemma germ_stalkClosedPointTo_Spec {R S : CommRingCat} [IsLocalRing S] (φ : R ⟶ S) :
    (Spec R).presheaf.germ ⊤ _ trivial ≫ stalkClosedPointTo (Spec.map φ) =
      (ΓSpecIso R).hom ≫ φ := by
  rw [stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc, ← Iso.inv_comp_eq,
    ← ΓSpecIso_inv_naturality_assoc]
  simp_rw [Opens.map_top]
  rw [germ_stalkClosedPointIso_hom, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h4v.s11.1496d9d3e997 from=seed src=0 shape=734ad429 vocab=07a31505
-/
@[reassoc]
lemma germ_stalkClosedPointTo (U : Opens X) (hU : f (closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo f = f.app U ≫
      ((Spec R).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem f hU).symm).op ≪≫
        ΓSpecIso R).hom := by
  rw [stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc, Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv, Category.assoc, ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h5v.s10.7bda5a90259c from=seed src=0 shape=95d7874a vocab=687eeb3d
-/
@[reassoc]
lemma germ_stalkClosedPointTo_Spec_fromSpecStalk
    {x : X} (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] (U : Opens X) (hU) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) =
      X.presheaf.germ U x (by simpa using hU) ≫ f := by
  have : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x := by
    rw [Hom.comp_apply, Spec_closedPoint, fromSpecStalk_closedPoint]
  have : x ∈ U := this ▸ hU
  simp only [germ_stalkClosedPointTo, Hom.comp_app,
    fromSpecStalk_app (X := X) (x := x) this, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
      (Spec.map f).app_eq_appLE, Hom.appLE_map_assoc, Hom.map_appLE_assoc]
  simp_rw [← Opens.map_top (Spec.map f).base]
  rw [← (Spec.map f).app_eq_appLE, ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.c65cadc96479 from=seed src=0 shape=2998fc4c vocab=b5353853
-/
lemma stalkClosedPointTo_fromSpecStalk (x : X) :
    stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (by rw [fromSpecStalk_closedPoint]; rfl)).hom := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  have : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by simp
  convert! germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 (X.presheaf.stalk x)) U hxU

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h3v.s9.480eefcf340d from=seed src=0 shape=16a63040 vocab=f7eeb266
-/
@[reassoc]
lemma Spec_stalkClosedPointTo_fromSpecStalk :
    Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (closedPoint R))) isOpen_univ
  have := IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, isoSpec_Spec_hom] at this
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc,
    germ_stalkClosedPointTo]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    Hom.app_eq_appLE, Hom.appLE_map_assoc, Spec.map_comp_assoc]

end Scheme

end stalkClosedPointTo

variable {R}

omit [IsLocalRing R] in
/-- useful lemma for applications of `SpecToEquivOfLocalRing`
@isnad1 id=iff.0h4v.s14.3dcff3e49987 from=seed src=0 shape=2ad33475 vocab=c4a288fb
-/
lemma SpecToEquivOfLocalRing_eq_iff
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }} :
    f₁ = f₂ ↔ ∃ h₁ : f₁.1 = f₂.1, f₁.2.1 =
      (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫ f₂.2.1 := by
  constructor
  · rintro rfl; simp
  · obtain ⟨x₁, ⟨f₁, h₁⟩⟩ := f₁
    obtain ⟨x₂, ⟨f₂, h₂⟩⟩ := f₂
    rintro ⟨rfl : x₁ = x₂, e : f₁ = _⟩
    simp [e]

variable (X R)

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
`(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/
@[simps]
noncomputable
def SpecToEquivOfLocalRing :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom } where
  toFun f := ⟨f (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    obtain ⟨x, ⟨f, hf⟩⟩ := xf
    symm
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨?_, ?_⟩
    · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Spec_closedPoint,
        Scheme.fromSpecStalk_closedPoint]
    · refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
      simp only [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk,
        TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc]

end AlgebraicGeometry
