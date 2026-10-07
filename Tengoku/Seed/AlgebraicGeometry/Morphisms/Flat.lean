/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.Ring.Under.Limits
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Affine
public import Tengoku.Seed.AlgebraicGeometry.Properties
public import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
public import Tengoku.Seed.RingTheory.RingHom.FaithfullyFlat

/-!
# Flat morphisms

A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).

We show that this property is local, and are stable under compositions and base change.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).
-/
@[mk_iff]
class Flat (f : X ⟶ Y) : Prop where
  flat_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Flat

/--
@isnad1 id=flat.3h5v.s9.5bbe27a1cd10 from=seed src=0 shape=3953db45 vocab=19175821
-/
alias Scheme.Hom.flat_appLE := Flat.flat_appLE

namespace Flat

instance : HasRingHomProperty @Flat RingHom.Flat where
  isLocal_ringHomProperty := RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff, affineLocally_iff_forall_isAffineOpen]

instance (priority := 900) [IsOpenImmersion f] : Flat f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.Flat.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @Flat :=
  HasRingHomProperty.stableUnderComposition RingHom.Flat.stableUnderComposition

/--
@isnad1 id=iff.0h3v.s5.cb8b4422e035 from=seed src=0 shape=110effa8 vocab=1653700d
-/
@[simp]
lemma SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} : Flat (Spec.map f) ↔ f.hom.Flat :=
  HasRingHomProperty.Spec_iff

/--
@isnad1 id=flat.0h5v.s5.7738c6ec4e57 from=seed src=0 shape=73d4a103 vocab=94f65908
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : Flat f] [hg : Flat g] : Flat (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

set_option backward.isDefEq.respectTransparency.types false in
instance : MorphismProperty.Respects @Flat @IsOpenImmersion where
  postcomp _ _ _ _ := inferInstance

instance : MorphismProperty.IsMultiplicative @Flat where
  id_mem _ := inferInstance

/--
@isnad1 id=isstable.0h0v.s2.197fbadac46c from=seed src=0 shape=25b03439 vocab=8c7654db
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Flat :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Flat.isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [Flat g] : Flat (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [Flat f] : Flat (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [Flat f] : Flat (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Flat f] : Flat (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/--
@isnad1 id=flat.1h3v.s9.a368c03665d4 from=seed src=0 shape=49937302 vocab=1ad225ce
-/
lemma of_stalkMap (H : ∀ x, (f.stalkMap x).hom.Flat) : Flat f :=
  HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime H

/--
@isnad1 id=flat.0h4v.s9.6145ca2a5be2 from=seed src=0 shape=f861e1e1 vocab=1ad225ce
-/
lemma stalkMap [Flat f] (x : X) : (f.stalkMap x).hom.Flat :=
  HasRingHomProperty.stalkMap (P := @Flat)
    (fun f hf J hJ ↦ hf.localRingHom J (J.comap f) rfl) ‹_› x

/--
@isnad1 id=iff.0h3v.s9.ac40ff917d71 from=seed src=0 shape=cfca0bf7 vocab=1ad225ce
-/
lemma iff_flat_stalkMap : Flat f ↔ ∀ x, (f.stalkMap x).hom.Flat :=
  ⟨fun _ ↦ stalkMap f, fun H ↦ of_stalkMap f H⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    [∀ i, Flat (f i)] : Flat (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)

set_option backward.isDefEq.respectTransparency false in
instance (priority := low) [Subsingleton Y] [IsIntegral Y] : Flat f := by
  refine (MorphismProperty.cancel_right_of_respectsIso @Flat _ Y.isoSpec.hom).mp ?_
  refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦ ?_
  rw [← Spec.map_preimage (X.affineCover.f i ≫ f ≫ Y.isoSpec.hom),
    HasRingHomProperty.Spec_iff (P := @Flat)]
  exact .of_isField (isField_of_isIntegral_of_subsingleton _) _

/-- A surjective, quasi-compact, flat morphism is a quotient map.
@isnad1 id=isquotie.0h3v.s7.07d6a8a748de from=seed src=0 shape=c9ce70f1 vocab=f460a177
-/
@[stacks 02JY]
lemma isQuotientMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] : Topology.IsQuotientMap f := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦
    ⟨fun hs ↦ ?_, fun hs ↦ hs.preimage f.continuous⟩, f.surjective⟩
  wlog hY : ∃ R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    refine this (f := pullback.fst (𝒰.f i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, pullback.condition,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
    refine this (f := (∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i)).isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (_ ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  · exact (surjective_iff (Spec.map φ)).mp inferInstance
  · apply RingHom.Flat.generalizingMap_comap
    rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

set_option backward.isDefEq.respectTransparency.types false in
/-- A flat surjective morphism of schemes is an epimorphism in the category of schemes.
@isnad1 id=epi.0h3v.s4.916140f7787b from=seed src=0 shape=2f814ce5 vocab=a5ffa051
-/
@[stacks 02VW]
lemma epi_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  apply ConcreteCategory.mono_of_injective
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iff.0h3v.s10.a1fb8fdbfe39 from=seed src=0 shape=38b2f8a2 vocab=7352a98a
-/
lemma flat_and_surjective_iff_faithfullyFlat_of_isAffine [IsAffine X] [IsAffine Y] :
    Flat f ∧ Surjective f ↔ f.appTop.hom.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective,
    MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f),
    MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f),
    ← HasRingHomProperty.Spec_iff (P := @Flat), surjective_iff]
  rfl

end Flat

/--
@isnad1 id=flat.0h3v.s10.7759b54b1b0d from=seed src=0 shape=25b3a774 vocab=256d8622
-/
lemma Scheme.Hom.flat_appTop [IsAffine X] [IsAffine Y] [Flat f] :
    f.appTop.hom.Flat :=
  HasRingHomProperty.appTop (P := @Flat) _ inferInstance

/--
@isnad1 id=iff.0h3v.s5.1058f01f2f7f from=seed src=0 shape=243a05c1 vocab=77b1f6fc
-/
lemma flat_and_surjective_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Flat (Spec.map f) ∧ Surjective (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat),
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, surjective_iff]
  rfl

section sections

/-!
## Sections of fibered products

Suppose we are given the following cartesian square:
```
Y --g-→ X
|       |
iY      iX
↓       |
T --f-→ S
```
Let `Uₛ` be an open of `S`, `Uₓ` and `Uₜ` be opens of `X` and `T` mapping into `Uₛ`.
There is a canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)`.

We show that this map is
1. `isIso_pushoutSection_of_isAffineOpen`:
  bijective when `Uₛ`, `Uₜ`, and `Uₓ` are all affine.
2. `mono_pushoutSection_of_isCompact_of_flat_right`:
  injective when `Uₛ`, `Uₜ` are affine, `Uₓ` is compact, and `f` is flat.
3. `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`:
  bijective when `Uₛ`, `Uₜ` are affine, `Uₓ` is qcqs, and `f` is flat.
4. `mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`:
  injective when `Uₛ` is affine, `Uₜ` is compact, `Uₓ` is qcqs, `f` is flat,
  and `Γ(T, Uₜ)` is flat over `Γ(S, Uₛ)` (typically true when `S = Spec k`.)
5. `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`:
  bijective when `Uₛ` is affine, `Uₜ` and `Uₓ` are qcqs, `f` is flat,
  and `Γ(T, Uₜ)` is flat over `Γ(S, Uₛ)` (typically true when `S = Spec k`.)

-/

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
  (H : IsPullback g iY iX f)
  {US : S.Opens} {UT : T.Opens}
  {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
  {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)

/-- The canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)`.
This is an isomorphism under various circumstances. -/
abbrev pushoutSection : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY) :=
  pushout.desc (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*]))
    (by simp only [Scheme.Hom.appLE_comp_appLE, H.w])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.4h12v.s10.3fb4857b3b8b from=seed src=0 shape=c92d5bc2 vocab=ca81cf87
-/
lemma isIso_pushoutSection_iff :
    IsIso (pushoutSection H hUST hUSX hUY) ↔ IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*])) :=
  ⟨fun _ ↦ .of_iso (.of_hasPushout _ _) (.refl _) (.refl _) (.refl _)
    (asIso (pushoutSection H hUST hUSX hUY)) (by simp) (by simp) (by simp) (by simp),
    fun h ↦ inferInstanceAs (IsIso h.isoPushout.inv)⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] IsAffineOpen.isoSpec_hom in
attribute [local simp ←] Scheme.Hom.resLE_eq_morphismRestrict in
/--
@isnad1 id=isiso.7h12v.s10.f5463673ed04 from=seed src=0 shape=ff87e573 vocab=ecea5d43
-/
lemma isIso_pushoutSection_of_isAffineOpen (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) : IsIso (pushoutSection H hUST hUSX hUY) := by
  refine (isIso_pushoutSection_iff ..).mpr (IsPullback.of_map_of_faithful Scheme.Spec ?_).unop
  have : IsAffine _ := hUS
  have : IsAffine _ := hUT
  have : IsAffine _ := hUX
  have hUY' : IsAffineOpen UY :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).isoPullback.hom
  exact .of_iso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).flip hUY'.isoSpec hUT.isoSpec
    hUX.isoSpec hUS.isoSpec (by simp) (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/--
@isnad1 id=mono.7h14v.s11.6f4f300d9cc6 from=seed src=0 shape=60c4919d vocab=b956c499
-/
lemma mono_pushoutSection_of_iSup_eq {ι : Type*} [Finite ι] (VX : ι → X.Opens) (hVU : iSup VX = UX)
    (hV : ∀ i, Mono (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ)
           |                          |
           ↓                          ↓
  Γ(X ×ₛ T, U ∩ Uₜ)  ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)
  ```
  -/
  have (i : _) : VX i ≤ iX ⁻¹ᵁ US := by clear hV; aesop
  classical
  algebraize [(iX.appLE US UX hUSX).hom, (f.appLE US UT hUST).hom]
  let (i : _) := (iX.appLE US (VX i) (by aesop)).hom.toAlgebra
  -- This is the map `Γ(X ×ₛ T, U ∩ Uₜ) ⟶ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)` on the bottom.
  let ψY : Γ(Y, UY) →+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) := RingHom.pi fun i ↦
      (Y.presheaf.map (homOfLE (by subst hUY hVU; gcongr; exact le_iSup _ _)).op).hom
  -- The map `Γ(X, U) ⟶ ∏ᵢ Γ(X, Vᵢ)`
  let ψ : Γ(X, UX) →ₐ[Γ(S, US)] Π i, Γ(X, VX i) := AlgHom.pi fun i ↦
    ⟨(X.presheaf.map (homOfLE (hVU ▸ le_iSup VX i)).op).hom, fun r ↦ by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]⟩
  -- ... is injective by the sheaf axiom,
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx ↦ ?_
    simp only [← hVU, Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est i)⟩
  -- ... and remains injective after tensoring with `Γ(T, Uₜ)` by the flatness assumption.
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  simp_rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at hV ⊢
  cases nonempty_fintype ι
  -- And the map at the right
  let φ : (Γ(T, UT) ⊗[Γ(S, US)] Π i, Γ(X, VX i)) →+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) :=
    (RingHom.pi fun i ↦ (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl).hom.comp
      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
      (by exact Pi.evalRingHom _ _))).comp (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).toRingHom
  -- ... is also injective by our hypotheses on `Vᵢ`.
  have hφ : Function.Injective φ := by
    dsimp [φ]
    refine .comp ?_ (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).injective
    exact .piMap fun i ↦ (hV _).comp <| CommRingCat.isPushout_tensorProduct _ _ _
      |>.flip.isoPushout.commRingCatIsoToRingEquiv.injective
  let e : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅
      .of (Γ(T, UT) ⊗[Γ(S, US)] Γ(X, UX)) :=
    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
  -- It remains to check that the square indeed commutes, and we may conclude that the map
  -- at the left is also injective.
  suffices (ψY.comp (pushoutSection H hUST hUSX hUY).hom).comp e.inv.hom = φ.comp
      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
    refine .of_comp (f := ψY) ?_
    convert (hφ.comp hψ').comp e.commRingCatIsoToRingEquiv.injective
    ext1 x; simpa using! congr($this (e.hom x))
  ext1
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
        (pushout.inr (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
    have H₂ (x j) : φ (x ⊗ₜ[↑Γ(S, US)] 1) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inr (C := CommRingCat) _ _ x) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inr_isoPushout_hom) x))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, ← CategoryTheory.comp_apply, pushoutSection]
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (pushout.inl (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
    have H₂ (x j) : φ (1 ⊗ₜ[↑Γ(S, US)] x) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inl (C := CommRingCat) _ _ (x j)) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inl_isoPushout_hom) (x j)))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection, ψ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isiso.8h14v.s12.0cb4837a2933 from=seed src=0 shape=11d69eaf vocab=318df9b3
-/
lemma isIso_pushoutSection_of_iSup_eq
    {ι : Type u} [Finite ι] (VX : ι → X.Opens) (hVU : iSup VX = UX)
    (hV : ∀ i, IsIso (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl))
    (hV' : ∀ i j, Mono (pushoutSection H hUST
      (show VX i ⊓ VX j ≤ _ from inf_le_left.trans (by clear hV; aesop)) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  classical
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  0 → Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ) ---→ Γ(T, Uₜ) ⊗ ∏ᵢⱼ Γ(X, Vᵢ ∩ Vⱼ)
           |                              |                           |
           ↓                              ↓                           ↓
  0 → Γ(X ×ₛ T, U ∩ Uₜ)  ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)  ---→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Vⱼ ∩ Uₜ)
  ```
  The two rows are exact because of the sheaf axiom (and additionally the flatness assumption for
  the top row). The vertical arrow in the middle is an isomorphism by assumption, and the one
  one the right is monomorphic by assumption. Hence the left arrow is also an isomorphism.

  In the actual proof we use `Pairwise`-indexed diagrams instead of nested limits because it works
  better with the existing API.
  -/
  -- The diagram consisting of `Γ(X, Vᵢ) ⟶ Γ(X, Vᵢ ∩ Vⱼ)`.
  let D := Pairwise.diagram VX
  have h : iSup D.obj = UX := by
    refine le_antisymm (iSup_le_iff.mpr ?_) ?_
    · subst hVU; rintro (i | ⟨i, j⟩); exacts [le_iSup VX _, inf_le_left.trans (le_iSup VX _)]
    · subst hVU; exact iSup_le_iff.mpr fun i ↦ le_iSup D.obj (.single i)
  let c₀ : Cocone D := (colimit.cocone _).extend
    (eqToIso (Y := UX) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  -- The diagram consisting of `Γ(T, Uₜ) ⊗ Γ(X, Vᵢ) ⟶ Γ(T, Uₜ) ⊗ Γ(X, Vᵢ ∩ Vⱼ)`.
  let F := Under.lift _ ((Functor.const _).map (iX.appLE US UX hUSX) ≫
    ((X.presheaf.mapCone c₀.op).π)) ⋙ Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _
  let G : X.Opens ⥤ Y.Opens :=
    { obj U := g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ UT, map h := homOfLE (by gcongr; exact h.le) }
  -- The natural transformation between the diagrams at the top and bottom.
  let αF : F ⟶ D.op ⋙ G.op ⋙ Y.presheaf :=
  { app i := (pushout.congrHom (by simp) rfl).hom ≫
      pushoutSection H hUST (by grw [← hUSX, ← h]; exact le_iSup D.obj i.unop) rfl }
  -- `Γ(T, Uₜ) ⊗ Γ(X, U)` as a (limit) cone over the top diagram.
  let c : Cone F := (Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) _)
  have := CommRingCat.Under.preservesFiniteLimits_of_flat _ hT
  cases nonempty_fintype ι
  let hc : IsLimit c :=
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf VX).preserves (c := c₀.op)
    haveI HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout _ ⋙ Under.forget _) (Under.isLimitLiftCone _ _ HX)
  let c'₀ : Cocone (D ⋙ G) := (colimit.cocone _).extend
    (eqToIso (Y := UY) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup]
      eta_expand
      dsimp [G]
      rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, h, hUY])).hom
  -- `Γ(X ×ₛ T, U ∩ Uₜ)` as a (limit) cone over the bottom diagram.
  let c' : Cone (D.op ⋙ G.op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' := by
    letI e : D ⋙ G ≅ Pairwise.diagram fun i ↦ g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => eqToIso (by
        dsimp [D, G]; rw [Scheme.Hom.preimage_inf, inf_inf_distrib_right]))
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i ↦ g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT)).preserves
        (c := ((Cocone.precompose e.inv).obj c'₀).op)
    exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cone.ext (.refl _)))
  have HαF₂ (i j : _) : Mono (αF.app (.op <| .pair i j)) := by infer_instance
  -- We construct the morphisms between the cone points,
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cone.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  -- and prove that they form an isomorphism.
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert! e.isIso_hom using 1
  · refine hc'.hom_ext fun i ↦ ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, Under.liftCone, c', c₀]
    · simp [αF, c, c']

/--
@isnad1 id=mono.7h12v.s10.fab920bf41d1 from=seed src=0 shape=f8d68251 vocab=05c6cdd5
-/
lemma mono_pushoutSection_of_isCompact_of_flat_right [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsCompact (X := X) UX) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq (ι := I) H hUST hUSX hUY (·) (by rwa [iSup_subtype, eq_comm])
    (fun i ↦ have := isIso_pushoutSection_of_isAffineOpen H hUST _ rfl hUS hUT i.1.2; inferInstance)
    (f.flat_appLE hUS hUT _)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=mono.7h12v.s10.0c96d3c8aab2 from=seed src=0 shape=4c374996 vocab=05c6cdd5
-/
lemma mono_pushoutSection_of_isCompact_of_flat_left [Flat iX]
    (hUS : IsAffineOpen US) (hUX : IsAffineOpen UX) (hUT : IsCompact (X := T) UT) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUX hUT

/--
@isnad1 id=isiso.8h12v.s10.7e874f98f83e from=seed src=0 shape=3c2e581b vocab=bdbd3956
-/
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_right [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have hIUX (i : I) : i.1 ≤ UX := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq H hUST hUSX hUY (fun i : I ↦ i) (by rwa [iSup_subtype,
    eq_comm]) (fun i ↦ isIso_pushoutSection_of_isAffineOpen _ _ _ _ hUS hUT i.1.2) (fun i j ↦
    mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUT (hUX' _ _ (hIUX _) i.1.1.2
    i.1.2.isCompact (hIUX _) j.1.1.2 j.1.2.isCompact))
    (f.flat_appLE hUS hUT _)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isiso.8h12v.s10.37b65e96e8c3 from=seed src=0 shape=0ad7509e vocab=bdbd3956
-/
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_left [Flat iX]
    (hUS : IsAffineOpen US) (hUX : IsAffineOpen UX)
    (hUT : IsCompact (X := T) UT) (hUT' : IsQuasiSeparated (α := T) UT) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ hUS hUX hUT hUT'

/--
@isnad1 id=mono.8h12v.s11.ca2dd17387f1 from=seed src=0 shape=e48b4673 vocab=0f00b4b3
-/
lemma mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat [Flat iX]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT)
    (hUX : IsCompact (X := X) UX) (hf : (f.appLE US UT hUST).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I ↦ i) (by rwa [iSup_subtype, eq_comm])
    (fun i ↦ mono_pushoutSection_of_isCompact_of_flat_left _ _ _ _ hUS i.1.2 hUT) hf

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=mono.8h12v.s11.3aa219c2aa82 from=seed src=0 shape=d2f3541c vocab=0f00b4b3
-/
lemma mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT)
    (hUX : IsCompact (X := X) UX) (hiX : (iX.appLE US UX hUSX).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX hUT hiX

set_option backward.isDefEq.respectTransparency false in
include H in
/--
@isnad1 id=isiso.10h12v.s11.895f8c380f05 from=seed src=0 shape=70751203 vocab=c2e77bde
-/
lemma isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT) (hUT' : IsQuasiSeparated (α := T) UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX)
    (hiX : (iX.appLE US UX hUSX).hom.Flat) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUT
  have hIUT (i : I) : i.1 ≤ UT := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I ↦ i) (by rwa [iSup_subtype, eq_comm])
    (fun i ↦ isIso_pushoutSection_of_isQuasiSeparated_of_flat_left _ _ _ _ hUS i.1.2 hUX hUX')
    (fun i j ↦ mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX
    (hUT' _ _ (hIUT _) i.1.1.2 i.1.2.isCompact (hIUT _) j.1.1.2 j.1.2.isCompact) hiX) hiX

end sections

end AlgebraicGeometry
