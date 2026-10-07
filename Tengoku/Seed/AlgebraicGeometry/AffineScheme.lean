/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Cover.Open
public import Tengoku.Seed.AlgebraicGeometry.GammaSpecAdjunction
public import Tengoku.Seed.AlgebraicGeometry.Restrict
public import Tengoku.Seed.CategoryTheory.Limits.Opposites
public import Tengoku.Seed.RingTheory.Localization.InvSubmonoid
public import Tengoku.Seed.RingTheory.LocalProperties.Basic
public import Tengoku.Seed.Topology.Sheaves.CommRingCat
public import Tengoku.Seed.CategoryTheory.Monad.Limits

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `AlgebraicGeometry.AffineScheme`: The category of affine schemes.
* `AlgebraicGeometry.IsAffine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.isoSpec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `AlgebraicGeometry.AffineScheme.equivCommRingCat`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRingCat`.
* `AlgebraicGeometry.IsAffineOpen`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `AlgebraicGeometry.IsAffineOpen.fromSpec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/-- The category of affine schemes -/
def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ

attribute [instance] IsAffine.affine

instance (X : Scheme.{u}) [IsAffine X] : IsIso (ΓSpec.adjunction.unit.app X) := @IsAffine.affine X _

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
@[simps! -isSimp hom]
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  asIso X.toSpecΓ

/--
@isnad1 id=eq.0h3v.s10.84f56a2d969c from=seed src=0 shape=fad09974 vocab=d4396f51
-/
@[reassoc]
theorem Scheme.isoSpec_hom_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (f.appTop) = f ≫ Y.isoSpec.hom := by
  simp only [isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

/--
@isnad1 id=eq.0h3v.s10.27b2881e6037 from=seed src=0 shape=69d747c7 vocab=54e61ac6
-/
@[reassoc]
theorem Scheme.isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.appTop) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp, isoSpec, asIso_hom, ← Scheme.toSpecΓ_naturality_assoc, isoSpec,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id]

/--
@isnad1 id=eq.0h1v.s8.cfb4542b5168 from=seed src=0 shape=dc223d19 vocab=d47dba10
-/
@[reassoc (attr := simp)]
lemma Scheme.toSpecΓ_isoSpec_inv (X : Scheme.{u}) [IsAffine X] :
    X.toSpecΓ ≫ X.isoSpec.inv = 𝟙 _ :=
  X.isoSpec.hom_inv_id

/--
@isnad1 id=eq.0h1v.s10.ac5b23cae6ba from=seed src=0 shape=721459dd vocab=d47dba10
-/
@[reassoc (attr := simp)]
lemma Scheme.isoSpec_inv_toSpecΓ (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv ≫ X.toSpecΓ = 𝟙 _ :=
  X.isoSpec.inv_hom_id

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typeclass version. -/
@[simps]
def AffineScheme.mk (X : Scheme) (_ : IsAffine X) : AffineScheme :=
  ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    AffineScheme.of X ⟶ AffineScheme.of Y :=
  InducedCategory.homMk f

/--
@isnad1 id=iff.0h1v.s3.e9a26083795a from=seed src=0 shape=052fb914 vocab=58dda572
-/
@[simp]
theorem essImage_Spec {X : Scheme} : Scheme.Spec.essImage X ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

/--
@isnad1 id=isaffine.0h1v.s4.aa0f39f8f6d0 from=seed src=0 shape=c7b20836 vocab=865e4082
-/
instance isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩

instance (R : CommRingCatᵒᵖ) : IsAffine (Scheme.Spec.obj R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage R⟩

/--
@isnad1 id=isaffine.0h1v.s2.207a3922856a from=seed src=0 shape=76a08d12 vocab=c983d273
-/
instance isAffine_Spec (R : CommRingCat) : IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩

/--
@isnad1 id=isaffine.0h3v.s4.cc902f4f6ba2 from=seed src=0 shape=f6911e5d vocab=18e376f6
-/
theorem IsAffine.of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← essImage_Spec] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h

/--
@isnad1 id=iff.0h3v.s4.f621d32c4708 from=seed src=0 shape=4c0b0746 vocab=18e376f6
-/
theorem IsAffine.iff_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsAffine X ↔ IsAffine Y :=
  ⟨fun _ ↦ .of_isIso (inv f), fun _ ↦ .of_isIso f⟩

/-- If `f : X ⟶ Y` is a morphism between affine schemes, the corresponding arrow is isomorphic
to the arrow of the morphism on prime spectra induced by the map on global sections. -/
noncomputable
def arrowIsoSpecΓOfIsAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Spec.map f.appTop) :=
  Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

/-- If `f : A ⟶ B` is a ring homomorphism, the corresponding arrow is isomorphic
to the arrow of the morphism induced on global sections by the map on prime spectra. -/
def arrowIsoΓSpecOfIsAffine {A B : CommRingCat} (f : A ⟶ B) :
    Arrow.mk f ≅ Arrow.mk ((Spec.map f).appTop) :=
  Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm

/--
@isnad1 id=eq.0h1v.s9.ff4bd15d5ca9 from=seed src=0 shape=ac0e545b vocab=956d975d
-/
theorem Scheme.isoSpec_Spec (R : CommRingCat.{u}) :
    (Spec R).isoSpec = Scheme.Spec.mapIso (Scheme.ΓSpecIso R).op :=
  Iso.ext (SpecMap_ΓSpecIso_hom R).symm

/--
@isnad1 id=eq.0h1v.s10.6eba78aab10d from=seed src=0 shape=7f56d54f vocab=25aaee3a
-/
@[simp] theorem Scheme.isoSpec_Spec_hom (R : CommRingCat.{u}) :
    (Spec R).isoSpec.hom = Spec.map (Scheme.ΓSpecIso R).hom :=
  (SpecMap_ΓSpecIso_hom R).symm

/--
@isnad1 id=eq.0h1v.s10.e61e8c5ef7fe from=seed src=0 shape=56e51dd8 vocab=bd3c6927
-/
@[simp] theorem Scheme.isoSpec_Spec_inv (R : CommRingCat.{u}) :
    (Spec R).isoSpec.inv = Spec.map (Scheme.ΓSpecIso R).inv :=
  congr($(isoSpec_Spec R).inv)

/--
@isnad1 id=eq.1h4v.s8.f3555c43a05f from=seed src=0 shape=d9a72267 vocab=c52b5fc2
-/
lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.appTop = g.appTop) :
    f = g := by
  rw [← cancel_mono Y.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

instance (P : MorphismProperty Scheme.{u}) {S : Scheme.{u}} (𝒰 : S.AffineCover P) (i : 𝒰.I₀) :
    IsAffine (𝒰.cover.X i) :=
  inferInstanceAs <| IsAffine (Spec _)

/-- `Scheme.Γ.rightOp : Scheme ⥤ CommRingCatᵒᵖ` preserves limits of diagrams consisting of
affine schemes. -/
instance preservesLimit_rightOp_Γ.{v, w}
    {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] :
    PreservesLimit D Scheme.Γ.rightOp := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  suffices PreservesLimit ((D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec) Scheme.Γ.rightOp from
    preservesLimit_of_iso_diagram _ (asIso α).symm
  have := monadicCreatesLimits.{v, w} Scheme.Spec.{u}
  suffices PreservesLimit (D ⋙ Scheme.Γ.rightOp) (Scheme.Spec ⋙ Scheme.Γ.rightOp) from
    preservesLimit_comp_of_createsLimit _ _
  exact preservesLimit_of_natIso _ (NatIso.op Scheme.SpecΓIdentity)

/-- `Scheme.Γ : Schemeᵒᵖ ⥤ CommRingCat` preserves colimits of diagrams consisting of
affine schemes. -/
instance preservesColimit_Γ.{v, w}
    {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}ᵒᵖ) [∀ i, IsAffine (D.obj i).unop] :
    PreservesColimit D Scheme.Γ := by
  have (i : _) : IsAffine (D.leftOp.obj i) := Functor.leftOp_obj D _ ▸ inferInstance
  exact preservesColimit_of_rightOp D Scheme.Γ

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage

/-! We copy over instances from `Scheme.Spec.toEssImage`. -/

/--
@isnad1 id=full.0h0v.s3.81d8f821d1a9 from=seed src=0 shape=836e6cbb vocab=de8068a8
-/
instance Spec_full : Spec.Full := Functor.Full.toEssImage _

/--
@isnad1 id=faithful.0h0v.s3.897db0e2f6db from=seed src=0 shape=836e6cbb vocab=fbbc8521
-/
instance Spec_faithful : Spec.Faithful := Functor.Faithful.toEssImage _

/--
@isnad1 id=esssurj.0h0v.s3.ae712b825851 from=seed src=0 shape=836e6cbb vocab=a78d6f58
-/
instance Spec_essSurj : Spec.EssSurj := Functor.EssSurj.toEssImage (F := _)

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps!]
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.Spec.essImage.ι

/-! We copy over instances from `Scheme.Spec.essImageInclusion`. -/

/--
@isnad1 id=full.0h0v.s2.566824d7d35f from=seed src=0 shape=54c8eceb vocab=d6fb986f
-/
instance forgetToScheme_full : forgetToScheme.Full :=
  inferInstanceAs Scheme.Spec.essImage.ι.Full

/--
@isnad1 id=faithful.0h0v.s2.eb1503be2200 from=seed src=0 shape=54c8eceb vocab=c9d8a524
-/
instance forgetToScheme_faithful : forgetToScheme.Faithful :=
  inferInstanceAs Scheme.Spec.essImage.ι.Faithful

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm

instance : Γ.{u}.rightOp.IsEquivalence := equivCommRingCat.isEquivalence_functor

instance : Γ.{u}.rightOp.op.IsEquivalence := equivCommRingCat.op.isEquivalence_functor

/--
@isnad1 id=isequiva.0h0v.s3.98fb36dd971f from=seed src=0 shape=836e6cbb vocab=166e8c08
-/
instance ΓIsEquiv : Γ.{u}.IsEquivalence :=
  inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence

/--
@isnad1 id=hascolim.0h0v.s1.5f0ee64ad10c from=seed src=0 shape=49959d42 vocab=d45172f1
-/
instance hasColimits : HasColimits AffineScheme.{u} :=
  haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  Adjunction.has_colimits_of_equivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse

/--
@isnad1 id=haslimit.0h0v.s1.7b9840bc94de from=seed src=0 shape=49959d42 vocab=50052a0d
-/
instance hasLimits : HasLimits AffineScheme.{u} := by
  have := Adjunction.has_colimits_of_equivalence Γ.{u}
  have : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.has_limits_of_equivalence (opOpEquivalence AffineScheme.{u}).inverse

/--
@isnad1 id=preserve.0h0v.s3.a3be4e05377f from=seed src=0 shape=43666dbc vocab=dad9f99e
-/
noncomputable instance Γ_preservesLimits : PreservesLimits Γ.{u}.rightOp := inferInstance

/--
@isnad1 id=preserve.0h0v.s2.6299fe0f929a from=seed src=0 shape=54c8eceb vocab=c7993572
-/
noncomputable instance forgetToScheme_preservesLimits : PreservesLimits forgetToScheme := by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Scheme.Spec)
  infer_instance

/-- The forgetful functor `AffineScheme ⥤ Scheme` creates small limits. -/
instance createsLimitsForgetToScheme : CreatesLimits forgetToScheme.{u} :=
  ⟨⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩⟩

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def IsAffineOpen {X : Scheme} (U : X.Opens) : Prop :=
  IsAffine U

/-- The set of affine opens as a subset of `opens X`. -/
def Scheme.affineOpens (X : Scheme) : Set X.Opens :=
  {U : X.Opens | IsAffineOpen U}

instance {Y : Scheme.{u}} (U : Y.affineOpens) : IsAffine U :=
  U.property

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isaffine.0h3v.s4.005a7495c16c from=seed src=0 shape=b45c8693 vocab=a59f738e
-/
theorem isAffineOpen_opensRange {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen f.opensRange := by
  refine .of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm

/--
@isnad1 id=isaffine.0h1v.s6.15aa4a323e49 from=seed src=0 shape=a305d14b vocab=37e148fb
-/
theorem isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : X.Opens) := by
  convert! isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm

/--
@isnad1 id=ex.1h3v.s7.e9e0a29ef460 from=seed src=0 shape=d8b60d01 vocab=efa22728
-/
theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}} {x : X}
    {U : X.Opens} (hxU : x ∈ U) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W.1 ⊆ U := by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩

/--
@isnad1 id=ex.0h2v.s8.019c3eb8ed98 from=seed src=0 shape=21eeb283 vocab=4175013d
-/
lemma Scheme.exists_Spec_apply_eq {X : Scheme.{u}} (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
    f.base y = x :=
  ⟨X.affineOpenCover.X _, X.affineOpenCover.f _, inferInstance, X.affineOpenCover.covers x⟩

/--
@isnad1 id=isaffine.0h2v.s4.1173dbe546d5 from=seed src=0 shape=91fa77d2 vocab=48a239f6
-/
instance Scheme.isAffine_affineCover (X : Scheme) (i : X.affineCover.I₀) :
    IsAffine (X.affineCover.X i) :=
  isAffine_Spec _

/--
@isnad1 id=isaffine.0h2v.s4.427b69222b1b from=seed src=0 shape=91fa77d2 vocab=30eb2acb
-/
instance Scheme.isAffine_affineBasisCover (X : Scheme) (i : X.affineBasisCover.I₀) :
    IsAffine (X.affineBasisCover.X i) :=
  isAffine_Spec _

/--
@isnad1 id=isaffine.0h3v.s4.a97c37b505eb from=seed src=0 shape=38ede395 vocab=ea4227f7
-/
instance Scheme.isAffine_affineOpenCover (X : Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀) :
    IsAffine (𝒰.openCover.X i) :=
  inferInstanceAs (IsAffine (Spec (𝒰.X i)))

instance (X : Scheme) [CompactSpace X] (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] (i) :
    IsAffine (𝒰.finiteSubcover.X i) :=
  inferInstanceAs (IsAffine (𝒰.X _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {X} [IsAffine X] (i) :
    IsAffine ((Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 X)).X i) := by
  dsimp; infer_instance

/--
@isnad1 id=isbasis.0h1v.s4.701196890e5d from=seed src=0 shape=0d65721e vocab=789fe1d4
-/
theorem Scheme.isBasis_affineOpens (X : Scheme) : Opens.IsBasis X.affineOpens := by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _

/--
@isnad1 id=eq.0h1v.s7.a9028d489adc from=seed src=0 shape=27c6d2fa vocab=88cd9477
-/
theorem iSup_affineOpens_eq_top (X : Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup]
  apply IsTopologicalBasis.sUnion_eq
  rw [← Set.image_eq_range]
  exact X.isBasis_affineOpens

/--
@isnad1 id=eq.0h2v.s11.57018c94ae27 from=seed src=0 shape=7f95c997 vocab=45b3a529
-/
theorem Scheme.map_PrimeSpectrum_basicOpen_of_affine
    (X : Scheme) [IsAffine X] (f : Γ(X, ⊤)) :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  Scheme.toSpecΓ_preimage_basicOpen _ _

/--
@isnad1 id=isbasis.0h1v.s8.fd564844b269 from=seed src=0 shape=a31f39e4 vocab=32faa4ec
-/
theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → X.Opens)) := by
  convert!
    PrimeSpectrum.isBasis_basic_opens.of_isInducing
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isInducing using 1
  ext V
  simp only [Set.mem_range, exists_exists_eq_and, Set.mem_ofPred,
    ← Opens.coe_inj (V := V), ← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

/-- The canonical map `U ⟶ Spec Γ(X, U)` for an open `U ⊆ X`. -/
noncomputable
def Scheme.Opens.toSpecΓ {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme ⟶ Spec Γ(X, U) :=
  U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s9.f2efc321cd89 from=seed src=0 shape=319ac652 vocab=f4b297bf
-/
@[reassoc (attr := simp)]
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map {X : Scheme} (U V : X.Opens) (h : U ≤ V) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE h).op) = X.homOfLE h ≫ V.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h2v.s11.e813678d4a32 from=seed src=0 shape=00c17041 vocab=557173b1
-/
@[reassoc] -- not simp because simp can prove this.
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top {X : Scheme} (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE le_top).op) = U.ι ≫ X.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality]

/--
@isnad1 id=eq.0h1v.s9.384b8b70232c from=seed src=0 shape=2d9fff1e vocab=4730ec83
-/
@[simp]
lemma Scheme.Opens.toSpecΓ_top {X : Scheme} :
    (⊤ : X.Opens).toSpecΓ = (⊤ : X.Opens).ι ≫ X.toSpecΓ := by
  simp [Scheme.Opens.toSpecΓ, toSpecΓ_naturality]; rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s13.b94c8034f82d from=seed src=0 shape=87b1ef27 vocab=947d70ac
-/
@[reassoc]
lemma Scheme.Opens.toSpecΓ_appTop {X : Scheme.{u}} (U : X.Opens) :
    U.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [Scheme.Opens.toSpecΓ]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s10.dbc8f4fb2f4b from=seed src=0 shape=cd2ac367 vocab=994bf5e1
-/
@[reassoc (attr := simp)]
lemma Scheme.Opens.toSpecΓ_naturality {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) = f ∣_ U ≫ U.toSpecΓ := by
  simp only [toSpecΓ, topIso, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    eqToHom_op, Hom.app_eq_appLE, Category.assoc, ← Spec.map_comp, Hom.appLE_map,
    toSpecΓ_naturality_assoc, TopologicalSpace.Opens.map_top, morphismRestrict_appLE, Hom.map_appLE]

/--
@isnad1 id=eq.1h5v.s10.6b5ec910da24 from=seed src=0 shape=6cb0bdd2 vocab=53604ceb
-/
@[reassoc (attr := simp)]
lemma Scheme.Opens.toSpecΓ_SpecMap_appLE
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hUV) :
    V.toSpecΓ ≫ Spec.map (f.appLE U V hUV) = f.resLE U V hUV ≫ U.toSpecΓ := by
  simp [Hom.appLE, Hom.resLE]

namespace IsAffineOpen

variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))

set_option backward.isDefEq.respectTransparency.types false in
attribute [-simp] eqToHom_op in
/-- The isomorphism `U ≅ Spec Γ(X, U)` for an affine `U`. -/
@[simps! -isSimp inv]
def isoSpec :
    ↑U ≅ Spec Γ(X, U) :=
  haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op

/--
@isnad1 id=eq.1h2v.s8.7777428509d0 from=seed src=0 shape=c7b28c98 vocab=3a77e246
-/
lemma isoSpec_hom : hU.isoSpec.hom = U.toSpecΓ := rfl

/--
@isnad1 id=eq.1h2v.s8.98daaf83567f from=seed src=0 shape=a4b25d07 vocab=39696f2f
-/
@[reassoc (attr := simp)]
lemma toSpecΓ_isoSpec_inv : U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _ := hU.isoSpec.hom_inv_id

/--
@isnad1 id=eq.1h2v.s9.96e62f6792d1 from=seed src=0 shape=e65167e6 vocab=39696f2f
-/
@[reassoc (attr := simp)]
lemma isoSpec_inv_toSpecΓ : hU.isoSpec.inv ≫ U.toSpecΓ = 𝟙 _ := hU.isoSpec.inv_hom_id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
/--
@isnad1 id=eq.1h3v.s11.705e206bf7a2 from=seed src=0 shape=8454d2b6 vocab=9e3299d3
-/
lemma isoSpec_hom_apply (x : U) :
    hU.isoSpec.hom x = Spec.map (X.presheaf.germ U x x.2) (closedPoint _) := by
  dsimp [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_apply, Scheme.Opens.toSpecΓ,
    TopCat.Presheaf.Γgerm]
  rw [← Scheme.Hom.comp_apply, ← Spec.map_comp,
    (Iso.eq_comp_inv _).mpr (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial),
    X.presheaf.germ_res_assoc, Spec.map_comp, Scheme.Hom.comp_apply]
  congr 1
  exact IsLocalRing.comap_closedPoint (U.stalkIso x).inv.hom

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h2v.s13.247465e2ebb5 from=seed src=0 shape=6b9329f8 vocab=567621df
-/
lemma isoSpec_hom_appTop :
    hU.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [isoSpec, Scheme.isoSpec]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h2v.s13.3b1c821406b6 from=seed src=0 shape=dd8e1b58 vocab=567621df
-/
lemma isoSpec_inv_appTop :
    hU.isoSpec.inv.appTop = U.topIso.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [← cancel_mono hU.isoSpec.hom.appTop, ← Scheme.Hom.comp_appTop, isoSpec_hom_appTop]
  simp
  rfl

/-- The open immersion `Spec Γ(X, U) ⟶ X` for an affine `U`. -/
def fromSpec :
    Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι

/--
@isnad1 id=isopenim.1h2v.s7.e6dac5a56a9f from=seed src=0 shape=6fc1227a vocab=b449b9d4
-/
instance isOpenImmersion_fromSpec :
    IsOpenImmersion hU.fromSpec := by
  delta fromSpec
  infer_instance

/--
@isnad1 id=eq.1h2v.s8.f87dd004bf93 from=seed src=0 shape=f0fd01a0 vocab=980d347b
-/
@[reassoc (attr := simp)]
lemma isoSpec_inv_ι : hU.isoSpec.inv ≫ U.ι = hU.fromSpec := rfl

/--
@isnad1 id=eq.1h2v.s8.92e3f74c099e from=seed src=0 shape=2feccc92 vocab=94ff579d
-/
@[reassoc (attr := simp)]
lemma isoSpec_hom_fromSpec : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  simp [← cancel_epi hU.isoSpec.inv]

/--
@isnad1 id=eq.1h2v.s7.8699d58be136 from=seed src=0 shape=562f1699 vocab=9864ec69
-/
@[reassoc (attr := simp)]
lemma toSpecΓ_fromSpec : U.toSpecΓ ≫ hU.fromSpec = U.ι := toSpecΓ_isoSpec_inv_assoc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h2v.s10.ddb4e5160063 from=seed src=0 shape=aa814654 vocab=fe2cd83c
-/
@[simp]
theorem range_fromSpec :
    Set.range hU.fromSpec = U := by
  delta IsAffineOpen.fromSpec; dsimp [IsAffineOpen.isoSpec_inv]
  rw [Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  · exact Subtype.range_coe
  rw [← TopCat.coe_comp, ← TopCat.epi_iff_surjective]
  infer_instance

/--
@isnad1 id=eq.1h2v.s11.1f78d39495ee from=seed src=0 shape=9821eb9b vocab=ee03f607
-/
@[reassoc (attr := simp)]
lemma fromSpec_toSpecΓ {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ X.toSpecΓ = Spec.map (X.presheaf.map (homOfLE le_top).op) := by
  rw [fromSpec, Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
    isoSpec_inv_toSpecΓ_assoc]

/--
@isnad1 id=eq.1h2v.s7.b20deb0a3f9a from=seed src=0 shape=68620623 vocab=6b9f1222
-/
@[simp]
theorem opensRange_fromSpec : hU.fromSpec.opensRange = U := Opens.ext (range_fromSpec hU)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.2h4v.s9.bc881674d042 from=seed src=0 shape=3126f6a8 vocab=d16c4a7e
-/
@[reassoc (attr := simp)]
theorem map_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V) :
    Spec.map (X.presheaf.map f) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine U := hU
  have : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec, ← X.homOfLE_ι (V := U) f.unop.le, isoSpec_inv, Category.assoc,
      ← Scheme.isoSpec_inv_naturality_assoc,
      ← Spec.map_comp_assoc, Scheme.homOfLE_appTop, ← Functor.map_comp]
  rw [fromSpec, isoSpec_inv, Category.assoc, ← Spec.map_comp_assoc, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.3h5v.s10.931b21a52ace from=seed src=0 shape=444a640e vocab=ad613be1
-/
@[reassoc]
lemma SpecMap_appLE_fromSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V i) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
  have : IsAffine U := hU
  simp only [IsAffineOpen.fromSpec, Category.assoc, isoSpec_inv]
  simp_rw [← Scheme.homOfLE_ι _ i]
  rw [Category.assoc, ← morphismRestrict_ι,
    ← Category.assoc _ (f ∣_ U) U.ι, ← @Scheme.isoSpec_inv_naturality_assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, Scheme.Hom.comp_appTop, morphismRestrict_appTop,
    Scheme.homOfLE_appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/--
@isnad1 id=eq.0h1v.s9.93272ea52264 from=seed src=0 shape=a73b856c vocab=9e6987bb
-/
lemma fromSpec_top [IsAffine X] : (isAffineOpen_top X).fromSpec = X.isoSpec.inv := by
  rw [fromSpec, Iso.inv_comp_eq]
  simp [isoSpec_hom]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.2h3v.s14.835aeec0fcb1 from=seed src=0 shape=2a821919 vocab=b2b14059
-/
lemma fromSpec_app_of_le (V : X.Opens) (h : U ≤ V) :
    hU.fromSpec.app V = X.presheaf.map (homOfLE h).op ≫
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec _).presheaf.map (homOfLE le_top).op := by
  have : U.ι ⁻¹ᵁ V = ⊤ := eq_top_iff.mpr fun x _ ↦ h x.2
  rw [IsAffineOpen.fromSpec, Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.Hom.app_eq _ this,
    ← Scheme.Hom.appTop, IsAffineOpen.isoSpec_inv_appTop]
  simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_hom,
    Category.assoc, ← X.presheaf.map_comp_assoc]
  rfl

include hU in
/--
@isnad1 id=iscompac.1h2v.s5.6ed41bcb8ec1 from=seed src=0 shape=8d60bb96 vocab=f1d21b50
-/
protected theorem isCompact :
    IsCompact (U : Set X) := by
  convert! @IsCompact.image _ _ _ _ Set.univ hU.fromSpec PrimeSpectrum.compactSpace.1 (by fun_prop)
  convert! hU.range_fromSpec.symm
  exact Set.image_univ

theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (f : X ⟶ Y) [H : IsOpenImmersion f] {U : X.Opens} :
    IsAffineOpen (f ''ᵁ U) ↔ IsAffineOpen U :=
  IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) (f ''ᵁ U).ι
    (by simp [Scheme.Hom.comp_base, Set.range_comp])).inv

include hU in
/--
@isnad1 id=isaffine.1h4v.s6.f7adad687a81 from=seed src=0 shape=69ad5f43 vocab=ac25ec91
-/
theorem image_of_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen (f ''ᵁ U) := by
  rwa [f.isAffineOpen_iff_of_isOpenImmersion]

/--
@isnad1 id=isaffine.1h4v.s6.203beb8ad1de from=seed src=0 shape=0c436121 vocab=80fee4b2
-/
theorem preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  haveI : IsAffine _ := hU
  .of_isIso (f ∣_ U)

/--
@isnad1 id=isaffine.2h4v.s7.d086ed772d85 from=seed src=0 shape=32a0a738 vocab=858ab773
-/
theorem preimage_of_isOpenImmersion {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsOpenImmersion f] (hU' : U ≤ f.opensRange) :
    IsAffineOpen (f ⁻¹ᵁ U) := by
  rwa [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr hU']

/-- The affine open sets of an open subscheme corresponds to
the affine open sets containing in the image. -/
@[simps]
def _root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv (f : X ⟶ Y) [H : IsOpenImmersion f] :
    X.affineOpens ≃o { U : Y.affineOpens // U ≤ f.opensRange } where
  toFun U := ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, U.1.2.preimage_of_isOpenImmersion _ U.2⟩
  left_inv _ := Subtype.ext (f.preimage_image_eq _)
  right_inv U := Subtype.ext (Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2)))
  map_rel_iff' := f.image_le_image_iff _ _

/-- The affine open sets of an open subscheme
corresponds to the affine open sets containing in the subset. -/
@[simps! apply_coe_coe]
def _root_.AlgebraicGeometry.affineOpensRestrict {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme.affineOpens ≃ { V : X.affineOpens // V ≤ U } :=
  (IsOpenImmersion.affineOpensEquiv U.ι).toEquiv.trans (Equiv.subtypeEquivProp (by simp))

@[simp]
lemma _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
    {X : Scheme.{u}} (U : X.Opens) (V) :
    ((affineOpensRestrict U).symm V).1 = U.ι ⁻¹ᵁ V := rfl

instance (priority := 100) _root_.AlgebraicGeometry.Scheme.compactSpace_of_isAffine
    (X : Scheme) [IsAffine X] :
    CompactSpace X :=
  ⟨(isAffineOpen_top X).isCompact⟩

/--
@isnad1 id=eq.1h2v.s12.c22bd84f632b from=seed src=0 shape=256de1f8 vocab=e20e1e2c
-/
@[simp]
theorem fromSpec_preimage_self :
    hU.fromSpec ⁻¹ᵁ U = ⊤ := by
  simp_rw [← hU.opensRange_fromSpec, Scheme.Hom.preimage_opensRange]

/--
@isnad1 id=eq.1h2v.s15.d561811543a4 from=seed src=0 shape=538db79b vocab=536fa5c4
-/
theorem ΓSpecIso_hom_fromSpec_app :
    (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  change _ = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
  simp [IsAffineOpen.fromSpec_app_of_le]

/--
@isnad1 id=eq.1h2v.s14.390c42035904 from=seed src=0 shape=d32b9353 vocab=b6fa1351
-/
@[elementwise]
theorem fromSpec_app_self :
    hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  rw [← hU.ΓSpecIso_hom_fromSpec_app, Iso.inv_hom_id_assoc]

/--
@isnad1 id=eq.1h3v.s14.e435ff824382 from=seed src=0 shape=b4473ca8 vocab=3e341e29
-/
theorem fromSpec_preimage_basicOpen' :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso Γ(X, U)).inv f) := by
  rw [Scheme.preimage_basicOpen, hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op

/--
@isnad1 id=eq.1h3v.s11.f7f68c1e4383 from=seed src=0 shape=16a5eeeb vocab=4570d64f
-/
theorem fromSpec_preimage_basicOpen :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f := by
  rw [fromSpec_preimage_basicOpen', ← basicOpen_eq_of_affine]

/--
@isnad1 id=eq.1h3v.s10.bd33eecb6020 from=seed src=0 shape=f6fe142d vocab=f4a70e63
-/
theorem fromSpec_image_basicOpen :
    hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen]
  ext1
  change hU.fromSpec '' hU.fromSpec ⁻¹' (X.basicOpen f : Set X) = _
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left, hU.range_fromSpec]
  exact Scheme.basicOpen_le _ _

/--
@isnad1 id=eq.1h3v.s13.5368cfbb5de7 from=seed src=0 shape=25de093f vocab=f92c8350
-/
@[simp]
theorem basicOpen_fromSpec_app :
    (Spec Γ(X, U)).basicOpen (hU.fromSpec.app U f) = PrimeSpectrum.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen, Scheme.preimage_basicOpen]

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/--
@isnad1 id=isaffine.1h3v.s7.959a55d85b39 from=seed src=0 shape=378b47c6 vocab=38c28cc7
-/
theorem basicOpen :
    IsAffineOpen (X.basicOpen f) := by
  rw [← hU.fromSpec_image_basicOpen, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert!
    isAffineOpen_opensRange
      (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm

/--
@isnad1 id=isaffine.0h2v.s4.4f45e93f507e from=seed src=0 shape=29498ad4 vocab=b3425b17
-/
lemma Spec_basicOpen {R : CommRingCat} (f : R) :
    IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen f) :=
  basicOpen_eq_of_affine f ▸ (isAffineOpen_top (Spec <| .of R)).basicOpen _

instance [IsAffine X] (r : Γ(X, ⊤)) : IsAffine (X.basicOpen r) :=
  (isAffineOpen_top X).basicOpen _

include hU in
/--
@isnad1 id=isaffine.1h3v.s10.a18d0b19bc8f from=seed src=0 shape=cb32fce6 vocab=f5f6ce87
-/
theorem ι_basicOpen_preimage (r : Γ(X, ⊤)) :
    IsAffineOpen ((X.basicOpen r).ι ⁻¹ᵁ U) := by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm,
    ← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

set_option backward.isDefEq.respectTransparency false in
include hU in
/--
@isnad1 id=ex.2h4v.s9.0b2f944220bf from=seed src=0 shape=7cbbf83f vocab=ba5c7fbc
-/
theorem exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x ∈ U) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f := by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂ : _ ≤ U.ι ⁻¹ᵁ V⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : (⟨x, h⟩ : U) ∈ _) (U.ι ⁻¹ᵁ V).isOpen
  replace h₁ : x.1 ∈ X.basicOpen r := by simpa [U.mem_basicOpen_toScheme] using! h₁
  replace h₂ : X.basicOpen r ≤ V := by
    simpa [Scheme.image_basicOpen] using! (U.ι.image_mono h₂).trans (U.ι.image_preimage_le _)
  exact ⟨U.topIso.hom.hom r, by simp [Scheme.Opens.toScheme_presheaf_obj, h₁, h₂]⟩

set_option backward.isDefEq.respectTransparency.types false in
noncomputable
instance {R : CommRingCat} {U} : Algebra R Γ(Spec R, U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.obj _))

/--
@isnad1 id=eq.0h2v.s11.6a509ecdf022 from=seed src=0 shape=daf9d354 vocab=b4e68fcd
-/
@[simp]
lemma algebraMap_Spec_obj {R : CommRingCat} {U} : algebraMap R Γ(Spec R, U) =
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
instance {R : CommRingCat} {f : R} :
    IsLocalization.Away f Γ(Spec R, PrimeSpectrum.basicOpen f) :=
  inferInstanceAs (IsLocalization.Away f
    ((Spec.structureSheaf R).obj.obj (op <| PrimeSpectrum.basicOpen f)))

/-- Given an affine open U and some `f : U`,
this is the canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(f))`
This is an isomorphism, as witnessed by an `IsIso` instance. -/
def basicOpenSectionsToAffine :
    Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen f) :=
  hU.fromSpec.app (X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom (hU.fromSpec_preimage_basicOpen f).symm).op

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isiso.1h3v.s11.e9def8904f6c from=seed src=0 shape=c3e1b47f vocab=7f8b7c50
-/
instance basicOpenSectionsToAffine_isIso :
    IsIso (basicOpenSectionsToAffine hU f) :=
  (hU.fromSpec.isIso_app _ (hU.opensRange_fromSpec.symm ▸ X.basicOpen_le f)).comp_isIso'
    inferInstance

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/--
@isnad1 id=away.1h3v.s9.56410124ab27 from=seed src=0 shape=3341b08a vocab=4b4900b6
-/
theorem isLocalization_basicOpen :
    IsLocalization.Away f Γ(X, X.basicOpen f) := by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
      (asIso <| basicOpenSectionsToAffine hU f).commRingCatIsoToRingEquiv).mpr
  convert! StructureSheaf.IsLocalization.to_basicOpen _ f using 1
  apply Algebra.algebra_ext
  intro _
  congr 1
  dsimp [CommRingCat.ofHom, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    basicOpenSectionsToAffine]
  rw [hU.fromSpec.naturality_assoc, hU.fromSpec_app_self]
  rfl

instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
    [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X, X.basicOpen r) :=
  isLocalization_basicOpen (isAffineOpen_top X) r

/--
@isnad1 id=eq.3h6v.s13.7c305d36f10a from=seed src=0 shape=9cacd937 vocab=047a4d4c
-/
lemma appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) :
    letI := hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r) := by
  let := hU.isLocalization_basicOpen r
  let := hV.isLocalization_basicOpen (f.appLE U V e r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map, CommRingCat.hom_ofHom, IsLocalization.map_comp,
    RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/--
@isnad1 id=eq.2h5v.s14.196fe4b371f3 from=seed src=0 shape=93c6959d vocab=54376eed
-/
lemma app_basicOpen_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    f.app (Y.basicOpen r) =
      (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op) := by
  have := hU.isLocalization_basicOpen r
  have := h.isLocalization_basicOpen (f.app U r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map, CommRingCat.hom_comp, RingHom.comp_assoc, CommRingCat.hom_ofHom,
    IsLocalization.map_comp, RingHom.algebraMap_toAlgebra,
    RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- `f.app (Y.basicOpen r)` is isomorphic to map induced on localizations
`Γ(Y, Y.basicOpen r) ⟶ Γ(X, X.basicOpen (f.app U r))` -/
def appBasicOpenIsoAwayMap {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    Arrow.mk (f.app (Y.basicOpen r)) ≅
      Arrow.mk (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)) :=
  Arrow.isoMk (Iso.refl _) (X.presheaf.mapIso (eqToIso (by simp)).op) <| by
    simp [hU.app_basicOpen_eq_away_map f h]
    rfl

include hU in
/--
@isnad1 id=away.2h5v.s11.5cc91d3961d6 from=seed src=0 shape=28a3079e vocab=2d436925
-/
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e; exact isLocalization_basicOpen hU f

instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
    (X : Scheme.{u}) [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X.basicOpen r, ⊤) :=
  (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.isOpenEmbedding_obj_top _)

include hU in
/--
@isnad1 id=ex.1h4v.s9.01f0e2ad755a from=seed src=0 shape=35f22567 vocab=38c28cc7
-/
theorem basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) :
    ∃ f' : Γ(X, U), X.basicOpen f' = X.basicOpen g := by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basicOpen_mul, Scheme.basicOpen_mul, RingHom.algebraMap_toAlgebra,
    Scheme.basicOpen_res]
  refine (inf_eq_left.mpr (inf_le_left.trans_eq (Scheme.basicOpen_of_isUnit _ ?_).symm)).symm
  exact
    Submonoid.leftInv_le_isUnit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (Γ(X, X.basicOpen f))
        _).prop

include hU in
theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
    {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f := by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable def primeIdealOf (x : U) :
    PrimeSpectrum Γ(X, U) :=
  hU.isoSpec.hom x

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h3v.s10.a294d2d4faeb from=seed src=0 shape=ec4a0a80 vocab=2f2d127b
-/
theorem fromSpec_primeIdealOf (x : U) :
    hU.fromSpec (hU.primeIdealOf x) = x.1 := by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

open IsLocalRing in
/--
@isnad1 id=eq.1h3v.s11.01106566ce28 from=seed src=0 shape=b5c2315a vocab=f19e0840
-/
theorem primeIdealOf_eq_map_closedPoint (x : U) :
    hU.primeIdealOf x = Spec.map (X.presheaf.germ _ x x.2) (closedPoint _) :=
  hU.isoSpec_hom_apply _

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.4h6v.s10.c4b6ad60b69c from=seed src=0 shape=86d47530 vocab=d67c4e40
-/
lemma comap_primeIdealOf_appLE {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    (hV.primeIdealOf ⟨x, hx⟩).comap (f.appLE U V hVU).hom = hU.primeIdealOf ⟨f x, hVU hx⟩ := by
  change Spec.map (f.appLE U V hVU) (hV.primeIdealOf ⟨x, hx⟩) = (hU.primeIdealOf ⟨f x, hVU hx⟩)
  simp only [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]
  simp only [Scheme.Hom.comp_apply]
  congr 1
  apply Subtype.ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- If a point `x : U` is a closed point, then its corresponding prime ideal is maximal.
@isnad1 id=ismaxima.2h3v.s10.2608ee85accd from=seed src=0 shape=341a0038 vocab=2ea5a085
-/
theorem primeIdealOf_isMaximal_of_isClosed (x : U) (hx : IsClosed {(x : X)}) :
    (hU.primeIdealOf x).asIdeal.IsMaximal := by
  have hx₀ : IsClosed {x} := by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective]
      using hx.preimage U.isOpenEmbedding'.continuous
  apply (hU.primeIdealOf x).isClosed_singleton_iff_isMaximal.mp
  rw [primeIdealOf, ← Set.image_singleton]
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed <|
    IsHomeomorph.isClosedEmbedding ?_).mp hx₀
  apply (TopCat.isIso_iff_isHomeomorph _).mp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=atprime.2h3v.s12.f855ec829fb7 from=seed src=0 shape=9dda160b vocab=00705419
-/
theorem isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    @IsLocalization.AtPrime
      (R := Γ(X, U))
      (S := X.presheaf.stalk <| hU.fromSpec y) _ _
      ((TopCat.Presheaf.algebra_section_stalk X.presheaf _)) y.asIdeal _ := by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_stalk Γ(X, U) y
  delta IsLocalization.AtPrime StructureSheaf.stalkAlgebra
  congr!
  simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, IsAffineOpen.fromSpec_app_self]
  rfl

/--
@isnad1 id=atprime.1h3v.s10.08cbbe38dd6a from=seed src=0 shape=9a8eb8ad vocab=39b4018a
-/
theorem isLocalization_stalk (x : U) :
    IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal := by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx

/--
@isnad1 id=injectiv.3h5v.s13.93071e389145 from=seed src=0 shape=41f9f6f2 vocab=9e470bd5
-/
lemma stalkMap_injective (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X)
    (hx : f x ∈ U)
    (h : ∀ g, f.stalkMap x (Y.presheaf.germ U (f x) hx g) = 0 →
      Y.presheaf.germ U (f x) hx g = 0) :
    Function.Injective (f.stalkMap x) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  apply (hU.isLocalization_stalk ⟨f x, hx⟩).injective_of_map_algebraMap_zero
  exact h

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/--
@isnad1 id=iff.1h4v.s12.d75b41bbcffb from=seed src=0 shape=3e033d13 vocab=5f159436
-/
lemma mem_ideal_iff {s : Γ(X, U)} {I : Ideal Γ(X, U)} :
    s ∈ I ↔ ∀ (x : X) (h : x ∈ U), X.presheaf.germ U x h s ∈ I.map (X.presheaf.germ U x h).hom := by
  refine ⟨fun hs x hxU ↦ Ideal.mem_map_of_mem _ hs, fun H ↦ ?_⟩
  let (x : _) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
      hU.isLocalization_stalk' ⟨P, hP⟩ (hU.isoSpec.inv _).2
  refine Submodule.mem_of_localization_maximal
      (fun P hP ↦ X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (fun P hP ↦ Algebra.linearMap _ _) _ _ ?_
  intro P hP
  rw [Ideal.localized₀_eq_restrictScalars_map]
  exact H _ _

include hU in
/--
@isnad1 id=iff.1h4v.s13.cc5f0c84706c from=seed src=0 shape=ea90b621 vocab=76944454
-/
lemma ideal_le_iff {I J : Ideal Γ(X, U)} :
    I ≤ J ↔ ∀ (x : X) (h : x ∈ U),
      I.map (X.presheaf.germ U x h).hom ≤ J.map (X.presheaf.germ U x h).hom :=
  ⟨fun h _ _ ↦ Ideal.map_mono h,
    fun H _ hs ↦ hU.mem_ideal_iff.mpr fun x hx ↦ H x hx (Ideal.mem_map_of_mem _ hs)⟩

include hU in
/--
@isnad1 id=iff.1h4v.s12.e7b93e4a8eb1 from=seed src=0 shape=ea90b621 vocab=dca79fa7
-/
lemma ideal_ext_iff {I J : Ideal Γ(X, U)} :
    I = J ↔ ∀ (x : X) (h : x ∈ U),
      I.map (X.presheaf.germ U x h).hom = J.map (X.presheaf.germ U x h).hom := by
  simp_rw [le_antisymm_iff, hU.ideal_le_iff, forall_and]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given affine opens `x ∈ V ⊆ f⁻¹(U)`, the stalk map of `f` at `x` is isomorphic to
`Localization.localRingHom` of `f.appLE U V`. -/
def arrowStalkMapIso (f : X ⟶ Y) {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
      (hx : x ∈ V) :
    Arrow.mk (f.stalkMap x) ≅ Arrow.mk (CommRingCat.ofHom <|
      Localization.localRingHom _ _ (f.appLE U V hVU).hom
        congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hx⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  refine Arrow.isoMk' _ _ ?_ ?_ ?_
  · exact ((IsLocalization.algEquiv (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
      (Y.presheaf.stalk (f x))
      (Localization.AtPrime (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)).toCommRingCatIso:)
  · exact ((IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x)
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)).toCommRingCatIso:)
  · rw [← Iso.comp_inv_eq]
    ext1
    apply IsLocalization.ringHom_ext
      (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
    ext a
    dsimp [← AlgEquiv.symm_toRingEquiv]
    simp only [IsLocalization.map_eq, RingHom.id_apply, Localization.localRingHom_to_map,
      RingHomCompTriple.comp_apply]
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]

/-- The basic open set of a section `f` on an affine open as an `X.affineOpens`. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.affineBasicOpen
    (X : Scheme) {U : X.affineOpens} (f : Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen f⟩

lemma _root_.AlgebraicGeometry.Scheme.affineBasicOpen_le
    (X : Scheme) {V : X.affineOpens} (f : Γ(X, V.1)) : X.affineBasicOpen f ≤ V :=
  X.basicOpen_le f

include hU in
/--
In an affine open set `U`, a family of basic open covers `U` iff the sections span `Γ(X, U)`.
See `iSup_basicOpen_of_span_eq_top` for the inverse direction without the affine-ness assumption.
@isnad1 id=iff.1h3v.s12.83f1377cdc1f from=seed src=0 shape=c5398d9a vocab=6b0c8486
-/
theorem iSup_basicOpen_eq_self_iff {s : Set Γ(X, U)} :
    ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal.span s = ⊤ := by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans hU.fromSpec ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 = hU.fromSpec ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec at h
      rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range, hU.range_fromSpec]
        at h
      simp only [Set.inter_self, Opens.carrier_eq_coe, Set.inter_eq_right] at h
      ext1
      refine Set.Subset.antisymm ?_ h
      simp only [Set.iUnion_subset_iff, SetCoe.forall, Opens.coe_iSup]
      intro x _
      exact X.basicOpen_le x
    · simp only [Opens.iSup_def, Set.preimage_iUnion]
      congr! 1
      · refine congr_arg (Set.iUnion ·) ?_
        ext1 x
        exact congr_arg Opens.carrier (hU.fromSpec_preimage_basicOpen _)
      · exact congr_arg Opens.carrier hU.fromSpec_preimage_self
  · simp only [Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [← Set.compl_iInter, Set.compl_univ_iff, ← PrimeSpectrum.zeroLocus_iUnion, ←
      PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span]
    simp only [Set.iUnion_singleton_eq_range, Subtype.range_val_subtype, Set.ofPred_mem_eq]

include hU in
/--
@isnad1 id=iff.1h3v.s12.946ca46d3777 from=seed src=0 shape=b68a3522 vocab=499a8b2b
-/
theorem self_le_iSup_basicOpen_iff {s : Set Γ(X, U)} :
    (U ≤ ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s = ⊤ := by
  rw [← hU.iSup_basicOpen_eq_self_iff, @comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x

end IsAffineOpen

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine open cover given by a covering family of affine opens. -/
@[simps I₀ X f]
def Scheme.AffineOpenCover.ofIsOpenCover {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    AffineOpenCover X where
  I₀ := ι
  X i := Γ(X, U i)
  f i := (hU' i).fromSpec
  idx x := (hU.exists_mem x).choose
  covers x :=
    ⟨(hU' _).isoSpec.hom ⟨_, (hU.exists_mem x).choose_spec⟩, by simp [← Scheme.Hom.comp_apply]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open _root_.PrimeSpectrum in
/-- The restriction of `Spec.map f` to a basic open `D(r)` is isomorphic to `Spec.map` of the
localization of `f` away from `r`. -/
noncomputable def SpecMapRestrictBasicOpenIso {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Arrow.mk (Spec.map f ∣_ (PrimeSpectrum.basicOpen r)) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom (Localization.awayMap f.hom r)) := by
  refine Arrow.isoMk ?_ ?_ ?_
  · exact (Spec _).isoOfEq (comap_basicOpen _ _) ≪≫ basicOpenIsoSpecAway (f.hom r)
  · exact basicOpenIsoSpecAway r
  · have hcomp : CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫
        CommRingCat.ofHom (Localization.awayMap f.hom r) =
        f ≫ CommRingCat.ofHom (algebraMap S (Localization.Away (f.hom r))) := by
      ext x
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R _)))]
    simp only [Arrow.mk_hom, Category.assoc, ← Spec.map_comp]
    simp [hcomp]

/--
@isnad1 id=injectiv.1h4v.s13.8231a58c701b from=seed src=0 shape=30e1629f vocab=0aa0901c
-/
lemma stalkMap_injective_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (x : X)
    (h : ∀ g, f.stalkMap x (Y.presheaf.Γgerm (f x) g) = 0 → Y.presheaf.Γgerm (f x) g = 0) :
    Function.Injective (f.stalkMap x) :=
  (isAffineOpen_top Y).stalkMap_injective f x trivial h

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a spanning set of `Γ(X, U)`, the corresponding basic open sets cover `U`.
See `IsAffineOpen.basicOpen_union_eq_self_iff` for the inverse direction for affine open sets.
@isnad1 id=eq.1h3v.s12.cd19546f8a37 from=seed src=0 shape=0c8a0f90 vocab=4b9cb434
-/
lemma iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) : (⨆ i ∈ s, X.basicOpen i) = U := by
  apply le_antisymm
  · rw [iSup₂_le_iff]
    exact fun i _ ↦ X.basicOpen_le i
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    refine SetLike.mem_of_subset ?_ hxV
    rw [← (hV.iSup_basicOpen_eq_self_iff (s := X.presheaf.map (homOfLE hVU).op '' s)).mpr
      (by rw [← Ideal.map_span, hs, Ideal.map_top])]
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Set.iUnion_coe_set, Set.mem_image,
      Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Scheme.basicOpen_res,
      Opens.coe_inf, Opens.coe_mk, Set.iUnion_subset_iff]
    exact fun i hi ↦ (Set.inter_subset_right.trans
      (Set.subset_iUnion₂ (s := fun x _ ↦ (X.basicOpen x : Set X)) i hi))

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea].
@isnad1 id=var.1h8v.s12.d2fbce830743 from=seed src=0 shape=9d4b3c08 vocab=fc37d03a
-/
@[elab_as_elim]
theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens → Prop}
    {ι} (U : ι → X.affineOpens) (iSup_U : (⨆ i, U i : X.Opens) = ⊤)
    (V : X.affineOpens)
    (basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)), P U → P (X.affineBasicOpen f))
    (openCover :
      ∀ (U : X.affineOpens) (s : Finset (Γ(X, U)))
        (_ : Ideal.span (s : Set (Γ(X, U))) = ⊤),
        (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hU : ∀ i, P (U i)) : P V := by
  have : ∀ (x : V.1), ∃ f : Γ(X, V), ↑x ∈ X.basicOpen f ∧ P (X.affineBasicOpen f) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (iSup_U.ge (Set.mem_univ x))
    obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop (U i).prop x ⟨x.prop, hi⟩
    refine ⟨f, hf, ?_⟩
    convert! basicOpen _ g (hU i) using 1
    ext1
    exact e
  choose f hf₁ hf₂ using this
  suffices Ideal.span (Set.range f) = ⊤ by
    obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp this
    apply openCover V t ht₂
    rintro ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := ht₁ hi
    exact hf₂ x
  rw [← V.prop.self_le_iSup_basicOpen_iff]
  intro x hx
  rw [iSup_range', Opens.mem_iSup]
  exact ⟨_, hf₁ ⟨x, hx⟩⟩

/-- If `φ` is a monomorphism in `CommRingCat`, it is not in general true that `Spec φ` is epi.
(`ℤ ⊆ ℤ[1/2]` but `Spec ℤ[1/2] ⟶ Spec ℤ` is not epi, since epi open immersions are isomorphisms)
But if the range of `f g : Spec R ⟶ X` are contained in an common affine open `U`, one can still
cancel `Spec.map φ ≫ f = Spec.map φ ≫ g` to get `f = g`. -/
lemma eq_of_SpecMap_comp_eq_of_isAffineOpen {R S : CommRingCat} {X : Scheme}
    (φ : R ⟶ S) (hφ : Function.Injective φ)
    {f g : Spec R ⟶ X} (U : X.Opens) (hU : IsAffineOpen U) (hUf : f ⁻¹ᵁ U = ⊤) (hUg : g ⁻¹ᵁ U = ⊤)
    (H : Spec.map φ ≫ f = Spec.map φ ≫ g) : f = g := by
  have : Mono φ := ConcreteCategory.mono_of_injective _ hφ
  rw [← IsOpenImmersion.lift_fac U.ι f (by simpa [Set.range_subset_iff] using fun x hx ↦ hUf.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by simpa [Set.range_subset_iff] using fun x hx ↦ hUg.ge hx)]
  congr 1
  rw [← cancel_mono hU.isoSpec.hom, ← Spec.homEquiv.injective.eq_iff,
    ← cancel_mono φ, ← Spec.map_injective.eq_iff]
  simp [← cancel_mono U.ι, H]

section ZeroLocus

namespace Scheme

open ConcreteCategory

variable (X : Scheme.{u})

/-- On a scheme `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` agrees with the associated zero locus on `X`.
@isnad1 id=eq.0h2v.s11.8e51515859a7 from=seed src=0 shape=ccd5efc2 vocab=db45d096
-/
lemma toSpecΓ_preimage_zeroLocus (s : Set Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocus s :=
  LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X` is affine, the image of the zero locus of global sections of `X` under `X.isoSpec`
is the zero locus in terms of the prime spectrum of `Γ(X, ⊤)`.
@isnad1 id=eq.0h2v.s11.40a14c4d5e64 from=seed src=0 shape=3b93cb00 vocab=21632f87
-/
lemma isoSpec_image_zeroLocus [IsAffine X]
    (s : Set Γ(X, ⊤)) :
    X.isoSpec.hom '' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← X.toSpecΓ_preimage_zeroLocus]
  simp [Scheme.isoSpec, Set.image_preimage_eq (h := (bijective_of_isIso _).surjective)]

/--
@isnad1 id=eq.0h2v.s11.4e63307c9de8 from=seed src=0 shape=d1aff552 vocab=3964c526
-/
lemma toSpecΓ_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.toSpecΓ '' X.zeroLocus s = PrimeSpectrum.zeroLocus s :=
  X.isoSpec_image_zeroLocus _

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s11.6da814ed3200 from=seed src=0 shape=00a8a420 vocab=692c7a97
-/
lemma isoSpec_inv_preimage_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← toSpecΓ_preimage_zeroLocus, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    X.isoSpec_inv_toSpecΓ]
  rfl

/--
@isnad1 id=eq.0h2v.s11.5a995b0b0ce3 from=seed src=0 shape=88442e43 vocab=0f00d31f
-/
lemma isoSpec_inv_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv '' PrimeSpectrum.zeroLocus s = X.zeroLocus s := by
  rw [← isoSpec_inv_preimage_zeroLocus, Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.inv.base).surjective

/-- If `X` is an affine scheme, every closed set of `X` is the zero locus
of a set of global sections. -/
lemma eq_zeroLocus_of_isClosed_of_isAffine [IsAffine X] (s : Set X) :
    IsClosed s ↔ ∃ I : Ideal Γ(X, ⊤), s = X.zeroLocus (U := ⊤) I := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · let Z : Set (Spec Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toSpecΓ_preimage_zeroLocus, ← hI, Z]
    symm
    exact Set.preimage_image_eq _ (bijective_of_isIso X.isoSpec.hom.base).injective
  · rintro ⟨I, rfl⟩
    exact zeroLocus_isClosed X I.carrier

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s11.ead965416758 from=seed src=0 shape=7f839254 vocab=3c94536f
-/
lemma Opens.toSpecΓ_preimage_basicOpen {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = U.ι ⁻¹ᵁ X.basicOpen r := by
  dsimp [toSpecΓ]
  simp only [Scheme.toSpecΓ_preimage_basicOpen, preimage_basicOpen, ι_app, homOfLE_leOfHom]
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.ι_preimage_self.symm).op,
    ← ConcreteCategory.comp_apply]
  congr 3
  simp [← Functor.map_comp]
  rfl

open Set.Notation in
/--
@isnad1 id=eq.0h3v.s10.89d447a26f05 from=seed src=0 shape=2c30ca55 vocab=da0708f9
-/
lemma Opens.toSpecΓ_preimage_zeroLocus {X : Scheme.{u}} (U : X.Opens) (s : Set Γ(X, U)) :
    U.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = U.1 ↓∩ X.zeroLocus s := by
  ext x
  refine .trans (forall₂_congr fun y hy ↦ ?_) Set.mem_iInter₂.symm
  exact iff_not_comm.mp congr(x ∈ $(Opens.toSpecΓ_preimage_basicOpen U y)).to_iff.symm

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h3v.s10.b4c7607537ff from=seed src=0 shape=cc330976 vocab=b8dca935
-/
lemma IsAffineOpen.fromSpec_preimage_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (∀ f ∈ s, ¬f ∉ x.asIdeal) ↔ s ⊆ x.asIdeal by
    simpa [← hU.fromSpec_image_basicOpen, -not_not] using! this
  simp_rw [not_not]
  rfl

/--
@isnad1 id=eq.1h3v.s10.161e8cf5874a from=seed src=0 shape=f0efe12a vocab=83953c6c
-/
lemma IsAffineOpen.fromSpec_image_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec '' PrimeSpectrum.zeroLocus s = X.zeroLocus s ∩ U := by
  rw [← hU.fromSpec_preimage_zeroLocus, Set.image_preimage_eq_inter_range, range_fromSpec]

set_option backward.isDefEq.respectTransparency false in
open Set.Notation in
/--
@isnad1 id=eq.0h4v.s13.234a48aa5265 from=seed src=0 shape=eeff51b4 vocab=f9734884
-/
lemma Scheme.zeroLocus_inf (X : Scheme.{u}) {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I ⊓ J) = X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J := by
  suffices U.1 ↓∩ (X.zeroLocus (U := U) ↑(I ⊓ J)) =
      U.1 ↓∩ (X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J) by
    ext x
    by_cases hxU : x ∈ U
    · simpa [hxU] using congr(⟨x, hxU⟩ ∈ $this)
    · simp only [Submodule.coe_inf, Set.mem_union,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I ∩ J)) hxU,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) I) hxU, true_or]
  simp only [← U.toSpecΓ_preimage_zeroLocus, PrimeSpectrum.zeroLocus_inf I J,
    Set.preimage_union]

/--
@isnad1 id=eq.1h5v.s13.0644138e4977 from=seed src=0 shape=3b4a27d3 vocab=f7f7f707
-/
lemma Scheme.zeroLocus_biInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) :
    X.zeroLocus (U := U) ↑(⨅ i ∈ t, I i) = (⋃ i ∈ t, X.zeroLocus (U := U) (I i)) ∪ (↑U)ᶜ := by
  refine ht.induction_on _ (by simp) fun {i t} hit ht IH ↦ ?_
  simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, ← IH, ← zeroLocus_inf,
    Submodule.coe_inf, Set.union_assoc]
  congr!
  simp

/--
@isnad1 id=eq.2h5v.s13.fd6a4fc5e789 from=seed src=0 shape=8418cb3e vocab=84eb0496
-/
lemma Scheme.zeroLocus_biInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) (ht' : t.Nonempty) :
    X.zeroLocus (U := U) ↑(⨅ i ∈ t, I i) = ⋃ i ∈ t, X.zeroLocus (U := U) (I i) := by
  rw [zeroLocus_biInf I ht, Set.union_eq_left]
  obtain ⟨i, hi⟩ := ht'
  exact fun x hx ↦ Set.mem_iUnion₂_of_mem hi
    (codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I i)) hx)

/--
@isnad1 id=eq.0h4v.s12.fc6dade5e8c6 from=seed src=0 shape=3c9937d8 vocab=aa697d58
-/
lemma Scheme.zeroLocus_iInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) [Finite ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = (⋃ i, X.zeroLocus (U := U) (I i)) ∪ (↑U)ᶜ := by
  simpa using zeroLocus_biInf I Set.finite_univ

/--
@isnad1 id=eq.0h4v.s12.bfec635f1b64 from=seed src=0 shape=0ecdde2c vocab=c01d1f2d
-/
lemma Scheme.zeroLocus_iInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) [Finite ι] [Nonempty ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = ⋃ i, X.zeroLocus (U := U) (I i) := by
  simpa using zeroLocus_biInf_of_nonempty I Set.finite_univ

end ZeroLocus

section Factorization

variable {X : Scheme.{u}} {A : CommRingCat}

/-- Given `f : X ⟶ Spec A` and some ideal `I ≤ ker(A ⟶ Γ(X, ⊤))`,
this is the lift to `X ⟶ Spec (A ⧸ I)`. -/
def Scheme.Hom.liftQuotient (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    X ⟶ Spec <| .of (A ⧸ I) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom hI))

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h4v.s12.5c220eb11de1 from=seed src=0 shape=67cf059a vocab=03f45718
-/
@[reassoc]
lemma Scheme.Hom.liftQuotient_comp (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    f.liftQuotient I hI ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = f := by
  rw [Scheme.Hom.liftQuotient, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.lift_comp_mk]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, ←
    Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom]
  simp

/-- If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `A ⧸ specTargetImage f`
is the scheme-theoretic image of `f`. For this quotient as an object of `CommRingCat` see
`specTargetImage` below. -/
def specTargetImageIdeal (f : X ⟶ Spec A) : Ideal A :=
  (RingHom.ker <| (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop.hom)

/-- If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `specTargetImage f` is the
scheme-theoretic image of `f` and `f` factors as
`specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f)`
(see `specTargetImageFactorization_comp`). -/
def specTargetImage (f : X ⟶ Spec A) : CommRingCat :=
  CommRingCat.of (A ⧸ specTargetImageIdeal f)

/-- If `f : X ⟶ Spec A` is a morphism of schemes, then `f` factors via
the inclusion of `Spec (specTargetImage f)` into `X`. -/
def specTargetImageFactorization (f : X ⟶ Spec A) : X ⟶ Spec (specTargetImage f) :=
  f.liftQuotient _ le_rfl

/-- If `f : X ⟶ Spec A` is a morphism of schemes, the induced morphism on spectra of
`specTargetImageRingHom f` is the inclusion of the scheme-theoretic image of `f` into `Spec A`. -/
def specTargetImageRingHom (f : X ⟶ Spec A) : A ⟶ specTargetImage f :=
  CommRingCat.ofHom (Ideal.Quotient.mk (specTargetImageIdeal f))

variable (f : X ⟶ Spec A)

/--
@isnad1 id=surjecti.0h3v.s7.66e2c2a71612 from=seed src=0 shape=8a739cde vocab=751cfbe7
-/
lemma specTargetImageRingHom_surjective : Function.Surjective (specTargetImageRingHom f) :=
  Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=injectiv.0h3v.s11.df16c60b070c from=seed src=0 shape=20dc53f9 vocab=8237dff7
-/
lemma specTargetImageFactorization_app_injective :
    Function.Injective <| (specTargetImageFactorization f).appTop := by
  let φ : A ⟶ Γ(X, ⊤) := (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop
  let φ' : specTargetImage f ⟶ Scheme.Γ.obj (op X) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
  change Function.Injective <| ((ΓSpec.adjunction.homEquiv X _) φ'.op).appTop
  rw [ΓSpec_adjunction_homEquiv_eq]
  apply (RingHom.kerLift_injective φ.hom).comp
  exact ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso _).hom).mp inferInstance).injective

/--
@isnad1 id=eq.0h3v.s5.cc5b697191d8 from=seed src=0 shape=407b2bf7 vocab=37692c91
-/
@[reassoc (attr := simp)]
lemma specTargetImageFactorization_comp :
    specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f) = f :=
  f.liftQuotient_comp _ _

end Factorization

section Stalks

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) (x : PrimeSpectrum R)

variable (R) (x : PrimeSpectrum R) in
/-- The stalk of `Spec R` at `x` is isomorphic to `Rₚ`,
where `p` is the prime corresponding to `x`. -/
noncomputable
def Spec.stalkIso : (Spec R).presheaf.stalk x ≅ .of (Localization.AtPrime x.asIdeal) :=
  (StructureSheaf.stalkIso ..).toCommRingCatIso.symm

/--
@isnad1 id=eq.0h2v.s10.f6265391f691 from=seed src=0 shape=c5aae107 vocab=b72aaa8d
-/
@[reassoc (attr := simp)]
lemma Spec.algebraMap_stalkIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (stalkIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial := by
  ext s : 2
  exact (IsLocalization.algEquiv _ ((structureSheaf R).presheaf.stalk _) _).symm.commutes s

/--
@isnad1 id=eq.0h2v.s11.023acbad9330 from=seed src=0 shape=9f4932e5 vocab=97857277
-/
@[reassoc (attr := simp)]
lemma Spec.germ_stalkMapIso_hom :
    (Spec R).presheaf.germ ⊤ _ trivial ≫ (stalkIso R x).hom =
      (Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (algebraMap R _) := by
  simp [← Iso.inv_comp_eq, ← Spec.algebraMap_stalkIso_inv_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Variant of `AlgebraicGeometry.localRingHom_comp_stalkIso` for `Spec.map`.
@isnad1 id=eq.0h4v.s10.7ab2d924b8cc from=seed src=0 shape=76f3fb5e vocab=9ffe7fbe
-/
@[elementwise]
lemma Scheme.localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (Spec.stalkIso R (p.comap f.hom)).hom ≫
      (CommRingCat.ofHom <| Localization.localRingHom
        (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal f.hom rfl) ≫
      (Spec.stalkIso S p).inv = (Spec.map f).stalkMap p :=
  AlgebraicGeometry.localRingHom_comp_stalkIso f p

set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of rings `f : R ⟶ S`, the stalk map of `Spec S ⟶ Spec R` at
a prime of `S` is isomorphic to the localized ring homomorphism. -/
def Scheme.arrowStalkMapSpecIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    Arrow.mk ((Spec.map f).stalkMap p) ≅ Arrow.mk (CommRingCat.ofHom <| Localization.localRingHom
      (p.comap f.hom).asIdeal p.asIdeal f.hom rfl) := Arrow.isoMk
  (Spec.stalkIso R (p.comap f.hom))
  (Spec.stalkIso S p) <| by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

end Stalks
end AlgebraicGeometry
