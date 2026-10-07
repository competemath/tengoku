/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Stalk
public import Tengoku.Seed.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!

# Residue fields of points

## Main definitions

The following are in the `AlgebraicGeometry.Scheme` namespace:

- `AlgebraicGeometry.Scheme.residueField`: The residue field of the stalk at `x`.
- `AlgebraicGeometry.Scheme.evaluation`: For open subsets `U` of `X` containing `x`,
  the evaluation map from sections over `U` to the residue field at `x`.
- `AlgebraicGeometry.Scheme.Hom.residueFieldMap`: A morphism of schemes induce a homomorphism of
  residue fields.
- `AlgebraicGeometry.Scheme.fromSpecResidueField`: The canonical map `Spec κ(x) ⟶ X`.
- `AlgebraicGeometry.Scheme.SpecToEquivOfField`: morphisms `Spec K ⟶ X` for a field `K` correspond
  to pairs of `x : X` with embedding `κ(x) ⟶ K`.


-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {U : X.Opens}

/-- The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`. -/
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)

instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (IsLocalRing.ResidueField (X.presheaf.stalk x))

instance (x : X) : Unique (Spec (X.residueField x)) := inferInstanceAs (Unique (Spec <| .of _))

/-- The residue map from the stalk to the residue field. -/
def residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

/-- See `AlgebraicGeometry.IsClosedImmersion.SpecMap_residue` for the stronger result that
`Spec.map (X.residue x)` is a closed immersion. -/
instance {X : Scheme.{u}} (x) : IsPreimmersion (Spec.map (X.residue x)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding
    (RingHom.surjectiveOnStalks_of_surjective (Ideal.Quotient.mk_surjective))

/--
@isnad1 id=eq.0h3v.s9.8a1f69d8f198 from=seed src=0 shape=010dfb7c vocab=b71ad23f
-/
@[simp]
lemma SpecMap_residue_apply {X : Scheme.{u}} (x : X) (s : Spec (X.residueField x)) :
    Spec.map (X.residue x) s = closedPoint (X.presheaf.stalk x) :=
  IsLocalRing.PrimeSpectrum.comap_residue _ s

/--
@isnad1 id=surjecti.0h2v.s8.d41dc4eea669 from=seed src=0 shape=8113dea4 vocab=b7a7db35
-/
lemma residue_surjective (X : Scheme.{u}) (x) : Function.Surjective (X.residue x) :=
  Ideal.Quotient.mk_surjective

instance (X : Scheme.{u}) (x) : Epi (X.residue x) :=
  ConcreteCategory.epi_of_surjective _ (X.residue_surjective x)

/-- If `K` is a field and `f : 𝒪_{X, x} ⟶ K` is a ring map, then this is the induced
map `κ(x) ⟶ K`. -/
def descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residueField x ⟶ .of K :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.lift (S := K) f.hom)

/--
@isnad1 id=eq.0h4v.s9.5f7674a021ce from=seed src=0 shape=2154282d vocab=5a8211e2
-/
@[reassoc (attr := simp)]
lemma residue_descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residue x ≫ X.descResidueField f = f :=
  CommRingCat.hom_ext <| RingHom.ext fun _ ↦ rfl

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
def evaluation (U : X.Opens) (x : X) (hx : x ∈ U) : Γ(X, U) ⟶ X.residueField x :=
  X.presheaf.germ U x hx ≫ X.residue _

/--
@isnad1 id=eq.1h3v.s8.fb95351595a4 from=seed src=0 shape=0c6f7847 vocab=e1612c6a
-/
@[reassoc]
lemma germ_residue (x hx) : X.presheaf.germ U x hx ≫ X.residue x = X.evaluation U x hx := rfl

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
abbrev Γevaluation (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  X.evaluation ⊤ x trivial

/--
@isnad1 id=iff.1h4v.s10.9832de2ab974 from=seed src=0 shape=ab1ea60a vocab=c793d1ce
-/
@[simp]
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f :=
  X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f

/--
@isnad1 id=iff.1h4v.s10.70ed2689fec5 from=seed src=0 shape=1897b6f7 vocab=c793d1ce
-/
lemma evaluation_ne_zero_iff_mem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f := by
  simp

/--
@isnad1 id=iff.0h3v.s11.cbd41f3bc493 from=seed src=0 shape=88b22765 vocab=5afafa40
-/
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.basicOpen f = ⊥ ↔ ∀ (x : U), X.evaluation U x x.property f = 0 :=
  X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero f

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def Hom.residueFieldMap (f : X ⟶ Y) (x : X) :
    Y.residueField (f x) ⟶ X.residueField x :=
  CommRingCat.ofHom <| IsLocalRing.ResidueField.map (f.stalkMap x).hom

/--
@isnad1 id=eq.0h4v.s9.4d1d21674f09 from=seed src=0 shape=ade35116 vocab=47052b21
-/
@[reassoc]
lemma residue_residueFieldMap (x : X) :
    Y.residue (f x) ≫ f.residueFieldMap x = f.stalkMap x ≫ X.residue x := by
  simp [Hom.residueFieldMap]
  rfl

/--
@isnad1 id=eq.0h2v.s7.d79ea9148a84 from=seed src=0 shape=99030884 vocab=cdc253f3
-/
@[simp]
lemma residueFieldMap_id (x : X) :
    Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  LocallyRingedSpace.residueFieldMap_id _

/--
@isnad1 id=eq.0h6v.s9.5151ef6323d3 from=seed src=0 shape=f77bc5f2 vocab=12186ebf
-/
@[simp]
lemma residueFieldMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x = g.residueFieldMap (f x) ≫ f.residueFieldMap x :=
  LocallyRingedSpace.residueFieldMap_comp _ _ _

/--
Degree of `f` at a point `x` is defined to be the degree of the associated field extension
from `κ(f x)` to `κ(x)`. We return a default value of zero when this degree is infinite.
-/
def Hom.residueDegree (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

/--
@isnad1 id=eq.0h2v.s4.12c97db767ec from=seed src=0 shape=e5543608 vocab=2ea3940e
-/
@[simp]
lemma Hom.residueDegree_id (x : X) : (𝟙 _ : X ⟶ X).residueDegree x = 1 := by
  dsimp [residueDegree]
  rw [residueFieldMap_id]
  exact CommSemiring.finrank_self _

/--
@isnad1 id=eq.1h5v.s10.3b2232e62f52 from=seed src=0 shape=3988188e vocab=8b6965fa
-/
@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : X) (hx : f x ∈ V) :
    Y.evaluation V (f x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx :=
  LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩

/--
@isnad1 id=eq.1h6v.s12.e2da5fe44959 from=seed src=0 shape=b6da71cc vocab=79fc2673
-/
lemma evaluation_naturality_apply {V : Opens Y} (x : X) (hx : f x ∈ V) (s) :
    f.residueFieldMap x (Y.evaluation V (f x) hx s) =
      X.evaluation (f ⁻¹ᵁ V) x hx (f.app V s) :=
  LocallyRingedSpace.evaluation_naturality_apply f.1 ⟨x, hx⟩ s

/--
@isnad1 id=eq.0h4v.s10.d5aacd9b8a85 from=seed src=0 shape=ecdc35f1 vocab=c4b32692
-/
@[reassoc]
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f x) ≫ f.residueFieldMap x = f.appTop ≫ X.Γevaluation x :=
  LocallyRingedSpace.Γevaluation_naturality f.toLRSHom x

/--
@isnad1 id=eq.0h5v.s12.574756ac395f from=seed src=0 shape=f56acd8a vocab=d25d54eb
-/
lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f x) a) = X.Γevaluation x (f.appTop a) :=
  LocallyRingedSpace.Γevaluation_naturality_apply f.toLRSHom x a

instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

section congr

-- replace this def if hard to work with
/-- The isomorphism between residue fields of equal points. -/
def residueFieldCongr {x y : X} (h : x = y) :
    X.residueField x ≅ X.residueField y :=
  eqToIso (by subst h; rfl)

/--
@isnad1 id=eq.0h2v.s5.b8cd23c9e742 from=seed src=0 shape=94c3b3d6 vocab=893cc0cb
-/
@[simp]
lemma residueFieldCongr_refl {x : X} :
    X.residueFieldCongr (refl x) = Iso.refl _ := rfl

/--
@isnad1 id=eq.1h3v.s6.e7226716737a from=seed src=0 shape=95887a24 vocab=1ee4ff87
-/
@[simp]
lemma residueFieldCongr_symm {x y : X} (e : x = y) :
    (X.residueFieldCongr e).symm = X.residueFieldCongr e.symm := rfl

/--
@isnad1 id=eq.1h3v.s6.473705648f98 from=seed src=0 shape=d9026342 vocab=2affd62d
-/
@[simp]
lemma residueFieldCongr_inv {x y : X} (e : x = y) :
    (X.residueFieldCongr e).inv = (X.residueFieldCongr e.symm).hom := rfl

/--
@isnad1 id=eq.2h4v.s6.28adbeba89f1 from=seed src=0 shape=10659f07 vocab=1c322a59
-/
@[simp]
lemma residueFieldCongr_trans {x y z : X} (e : x = y) (e' : y = z) :
    X.residueFieldCongr e ≪≫ X.residueFieldCongr e' = X.residueFieldCongr (e.trans e') := by
  subst e e'
  rfl

/--
@isnad1 id=eq.2h4v.s7.3f7ecf2a9d48 from=seed src=0 shape=8cdd177b vocab=1e72e966
-/
@[reassoc (attr := simp)]
lemma residueFieldCongr_trans_hom (X : Scheme) {x y z : X} (e : x = y) (e' : y = z) :
    (X.residueFieldCongr e).hom ≫ (X.residueFieldCongr e').hom =
      (X.residueFieldCongr (e.trans e')).hom := by
  subst e e'
  rfl

/--
@isnad1 id=eq.1h3v.s7.84e4bdd51817 from=seed src=0 shape=6ffb4d27 vocab=43769408
-/
@[reassoc]
lemma residue_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.residue x ≫ (X.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.residue y := by
  subst h
  simp

/--
@isnad1 id=eq.1h5v.s10.8dedf9739b14 from=seed src=0 shape=8623378f vocab=62e0c61c
-/
lemma Hom.residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x = (Y.residueFieldCongr (by subst e; rfl)).hom ≫ g.residueFieldMap x := by
  subst e; simp

/--
@isnad1 id=eq.1h5v.s10.2d99ca41778b from=seed src=0 shape=b8101bbb vocab=6298c961
-/
@[reassoc]
lemma Hom.residueFieldMap_congr' {f : X ⟶ Y} {x₁ x₂ : X} (e : x₁ = x₂) :
    f.residueFieldMap x₁ ≫ (X.residueFieldCongr e).hom =
      (Y.residueFieldCongr (congrArg f e)).hom ≫ f.residueFieldMap x₂ := by
  subst e
  simp

end congr

section fromResidueField

/-- The canonical map `Spec κ(x) ⟶ X`. -/
def fromSpecResidueField (X : Scheme) (x : X) :
    Spec (X.residueField x) ⟶ X :=
  Spec.map (X.residue x) ≫ X.fromSpecStalk x

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecResidueField x) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [IsPreimmersion.comp_iff]
  infer_instance

@[simps] noncomputable
instance (x : X) : (Spec (X.residueField x)).Over X := ⟨X.fromSpecResidueField x⟩

noncomputable
instance (x : X) : (Spec (X.residueField x)).CanonicallyOver X where

/--
@isnad1 id=eq.1h3v.s6.6f81b1a43568 from=seed src=0 shape=9da4f2f2 vocab=d190ba2a
-/
@[reassoc (attr := simp)]
lemma residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) :
    Spec.map (X.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ =
      X.fromSpecResidueField _ := by
  subst h; simp

instance {x y : X} (h : x = y) : (Spec.map (X.residueFieldCongr h).hom).IsOver X where

/--
@isnad1 id=eq.0h4v.s9.d069f950af1f from=seed src=0 shape=6bd67e95 vocab=e34797ae
-/
@[reassoc (attr := simp)]
lemma Hom.SpecMap_residueFieldMap_fromSpecResidueField (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc, ← SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  rfl

instance [X.Over Y] (x : X) : Spec.map ((X ↘ Y).residueFieldMap x) |>.IsOver Y where

/--
@isnad1 id=eq.0h3v.s7.c6005de9a117 from=seed src=0 shape=abdb4a6b vocab=0c0051c8
-/
@[simp]
lemma fromSpecResidueField_apply (x : X.carrier) (s : Spec (X.residueField x)) :
    X.fromSpecResidueField x s = x := by
  simp [fromSpecResidueField]

/--
@isnad1 id=eq.0h2v.s8.a480cf0775bd from=seed src=0 shape=41c30b84 vocab=0fdbb50f
-/
lemma range_fromSpecResidueField (x : X.carrier) :
    Set.range (X.fromSpecResidueField x) = {x} := by
  simp

/--
@isnad1 id=eq.0h4v.s9.70a1dd90eafd from=seed src=0 shape=0bae9e5e vocab=ebe74ff5
-/
lemma descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    Spec.map (X.descResidueField f) ≫
      X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x := by
  simp [fromSpecResidueField, ← Spec.map_comp_assoc]

/--
@isnad1 id=eq.0h3v.s9.8316c57d784b from=seed src=0 shape=3864295e vocab=4481108d
-/
lemma descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) :
    Spec.map (descResidueField (Scheme.stalkClosedPointTo f)) ≫
      X.fromSpecResidueField (f (closedPoint K)) = f := by
  rw [X.descResidueField_fromSpecResidueField, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

end fromResidueField

section Spec

variable (R : CommRingCat) (x : Spec R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue fields of `Spec R` are isomorphic to `Ideal.ResidueField`. -/
noncomputable
def Spec.residueFieldIso :
    (Spec R).residueField x ≅ .of x.asIdeal.ResidueField :=
  (IsLocalRing.ResidueField.mapEquiv
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv).toCommRingCatIso

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.993a525fbc4a from=seed src=0 shape=f6742ea6 vocab=28f787a0
-/
@[reassoc (attr := simp)]
lemma Spec.algebraMap_residueFieldIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (residueFieldIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial ≫ (Spec R).residue x := by
  rw [← Spec.algebraMap_stalkIso_inv_assoc]; rfl

/--
@isnad1 id=eq.0h2v.s10.2df309607430 from=seed src=0 shape=283713bd vocab=e1f6f340
-/
@[reassoc (attr := simp)]
lemma Spec.residue_residueFieldIso_hom :
    (Spec R).residue x ≫ (residueFieldIso R x).hom =
      (Spec.stalkIso R x).hom ≫ CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s10.84b00cd590dc from=seed src=0 shape=d960c073 vocab=e47ce03b
-/
@[reassoc (attr := simp)]
lemma Spec.map_residueFieldIso_inv_eq_fromSpecResidueField :
    Spec.map (residueFieldIso _ _).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) =
    (Spec R).fromSpecResidueField x := by
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rw [Spec.map_inj]
  simp [← Scheme.Spec.algebraMap_residueFieldIso_inv]

end Spec

/-- A helper lemma to work with `AlgebraicGeometry.Scheme.SpecToEquivOfField`.
@isnad1 id=iff.0h4v.s9.52711cfd5077 from=seed src=0 shape=a57f1423 vocab=52ebec32
-/
lemma SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme}
    {f₁ f₂ : Σ x : X.carrier, X.residueField x ⟶ .of K} :
    f₁ = f₂ ↔ ∃ e : f₁.1 = f₂.1, f₁.2 = (X.residueFieldCongr e).hom ≫ f₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨f, _⟩ := f₁
    obtain ⟨g, _⟩ := f₂
    rintro ⟨(rfl : f = g), h⟩
    simpa

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field `K` and a scheme `X`, the morphisms `Spec K ⟶ X` bijectively correspond
to pairs of points `x` of `X` and embeddings `κ(x) ⟶ K`. -/
@[simps]
def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv f := by
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      Scheme.fromSpecResidueField_apply, exists_true_left]
    rw [← Spec.map_inj, Spec.map_comp, ← cancel_mono (X.fromSpecResidueField _)]
    grind [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField,
      Scheme.fromSpecResidueField_apply,
      Scheme.residueFieldCongr_fromSpecResidueField]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h5v.s10.575579864744 from=seed src=0 shape=8e8d5afc vocab=a902c5f4
-/
@[simp]
lemma descResidueField_stalkClosedPointTo_comp {K : Type u} [Field K] (g : Spec (.of K) ⟶ X) :
    dsimp% descResidueField (stalkClosedPointTo (g ≫ f)) =
      Hom.residueFieldMap f (g (closedPoint K)) ≫ descResidueField (stalkClosedPointTo g) := by
  simp [← cancel_epi (Y.residue _), stalkClosedPointTo_comp, residue_residueFieldMap_assoc]

end Scheme

end AlgebraicGeometry
