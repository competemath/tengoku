/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
public import Tengoku.Seed.CategoryTheory.Limits.Constructions.Over.Basic
public import Tengoku.Seed.CategoryTheory.Limits.Constructions.Over.Products
public import Tengoku.Seed.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immersion.

## Main definitions
- `AlgebraicGeometry.IsSeparated`: The class of separated morphisms.
- `AlgebraicGeometry.Scheme.IsSeparated`: The class of separated schemes.
- `AlgebraicGeometry.IsSeparated.hasAffineProperty`:
  A morphism is separated iff the preimage of affine opens are separated schemes.
-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is separated if the diagonal map is a closed immersion. -/
@[mk_iff]
class IsSeparated : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f) := by infer_instance

namespace IsSeparated

attribute [instance] isClosedImmersion_diagonal

/--
@isnad1 id=eq.0h0v.s4.74ccfe172fd0 from=seed src=0 shape=d9c52ade vocab=e7df127a
-/
theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

/-- Monomorphisms are separated.
@isnad1 id=issepara.0h3v.s4.8c29d6658faa from=seed src=0 shape=31ca8f87 vocab=2c384382
-/
instance (priority := 900) isSeparated_of_mono [Mono f] : IsSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
instance : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (priority := 900) [IsSeparated f] : QuasiSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isstable.0h0v.s2.dd7d1e38709d from=seed src=0 shape=25b03439 vocab=21cbdb50
-/
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance

instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isstable.0h0v.s2.d175654d1258 from=seed src=0 shape=25b03439 vocab=516e0a65
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance : IsZariskiLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g] :
    IsSeparated (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f] :
    IsSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [IsSeparated f] : IsSeparated (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [IsSeparated f] :
    IsSeparated (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

instance (R S : CommRingCat.{u}) (f : R ⟶ S) : IsSeparated (Spec.map f) := by
  constructor
  let := f.hom.toAlgebra
  change IsClosedImmersion
    (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [diagonal_SpecMap, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  exact .spec_of_surjective _ fun x ↦ ⟨.tmul R 1 x,
    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=issepara.0h3v.s4.55dc319c3c42 from=seed src=0 shape=892cb9de vocab=06081645
-/
@[instance 100]
lemma of_isAffineHom [h : IsAffineHom f] : IsSeparated f := by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsZariskiLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h
  rw [MorphismProperty.arrow_mk_iso_iff @IsSeparated (arrowIsoSpecΓOfIsAffine f)]
  infer_instance

instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [IsSeparated i] :
    IsClosedImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i)
    inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Given `f : X ⟶ Y` and `g : Y ⟶ Z` such that `g` is separated, the induced map
`X ⟶ X ×[Z] Y` is a closed immersion. -/
instance [IsSeparated g] :
    IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ g))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstance : IsClosedImmersion (pullback.mapDesc f (𝟙 _) g))
  ext : 1 <;> simp [pullback.condition]

end IsSeparated

section of_injective

open Scheme Pullback

variable (𝒰 : Y.OpenCover) (𝒱 : ∀ i, (pullback f (𝒰.f i)).OpenCover)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h5v.s8.aae9eb2797fe from=seed src=0 shape=395bd676 vocab=1ae06540
-/
lemma Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective
    (hf : Function.Injective f) :
    diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.mem_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  have H : pullback.fst f f x = pullback.snd f f x :=
    hf (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  let i := 𝒰.idx (f (pullback.fst f f x))
  obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f _⟩ :=
    𝒰.covers (f (pullback.fst f f x))
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).idx z
  obtain ⟨w : (𝒱 i).X j, hy : (𝒱 i).f j w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, ?_⟩
  simp_rw [diagonalCover_map]
  change x ∈ Set.range _
  simp only [diagonalCover, openCoverOfBase_I₀,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    Precoverage.ZeroHypercover.bind_toPreZeroHypercover, openCoverOfBase_X,
    PreZeroHypercover.bind_X, openCoverOfLeftRight_I₀, openCoverOfLeftRight_X]
  rw [range_map]
  simp [← H, ← hz₁, ← hy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=le.0h5v.s8.42dadfcae068 from=seed src=0 shape=79645093 vocab=8f6806f4
-/
lemma Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange :
    Set.range (pullback.diagonal f) ⊆ diagonalCoverDiagonalRange f 𝒰 𝒱 := by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  let i := 𝒰.idx (f x)
  obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f x⟩ := 𝒰.covers (f x)
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).idx z
  obtain ⟨w : (𝒱 i).X j, hy : (𝒱 i).f j w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, pullback.diagonal ((𝒱 i).f j ≫ pullback.snd f (𝒰.f i)) w, ?_⟩
  rw [← hz₁, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  simp only [diagonalCover, openCoverOfBase_I₀,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    Cover.pullbackHom, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, openCoverOfBase_X,
    PreZeroHypercover.bind_X, openCoverOfLeftRight_I₀, openCoverOfLeftRight_X,
    PreZeroHypercover.bind_f, openCoverOfLeftRight_f, openCoverOfBase_f, Hom.comp_base,
    TopCat.hom_comp, ContinuousMap.comp_apply, ContinuousMap.comp_assoc]
  simp_rw [← Scheme.Hom.comp_apply]
  congr 5
  apply pullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isclosed.0h5v.s9.5ab7f9764246 from=seed src=0 shape=c2b9202e vocab=14fff715
-/
lemma isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange
    [∀ i, IsAffine (𝒰.X i)] [∀ i j, IsAffine ((𝒱 i).X j)] :
    IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonalRange f 𝒰 𝒱) := by
  let U : (Σ i, (𝒱 i).I₀) → (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i ↦
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right, Opens.opensRange_ι]
    exact le_iSup (fun i : Σ i, (𝒱 i).I₀ ↦ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange) i
  have hf : iSup U = ⊤ := (TopologicalSpace.Opens.map_iSup _ _).symm.trans
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι_preimage_self
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hf]
  intro i
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictRestrict _ _ _),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictEq _ (hU i)),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (diagonalRestrictIsoDiagonal ..)]
  infer_instance

/--
@isnad1 id=issepara.1h3v.s7.ef249dad0d51 from=seed src=0 shape=33fd3be7 vocab=5fae850f
-/
@[stacks 0DVA]
lemma isSeparated_of_injective (hf : Function.Injective f) :
    IsSeparated f := by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} ↦ ⊤) (by simp) fun _ ↦ ?_
  rw [← diagonalCoverDiagonalRange_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱

end of_injective

instance : MorphismProperty.HasOfPostcompProperty @IsClosedImmersion @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsClosedImmersion _)

/--
@isnad1 id=isclosed.0h5v.s5.3b1156508862 from=seed src=0 shape=77972de3 vocab=f06b81db
-/
lemma IsClosedImmersion.of_comp [IsClosedImmersion (f ≫ g)] [IsSeparated g] :
    IsClosedImmersion f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

variable {f g} in
/--
@isnad1 id=iff.0h5v.s5.66b93fb0eb11 from=seed src=0 shape=daa213a1 vocab=244eec3d
-/
lemma IsClosedImmersion.comp_iff [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) ↔ IsClosedImmersion f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

instance {I J : X.IdealSheafData} (h : I ≤ J) : IsClosedImmersion (I.inclusion h) := by
  have : IsClosedImmersion (I.inclusion h ≫ I.subschemeι) := by
    simp only [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  exact .of_comp _ I.subschemeι

/--
@isnad1 id=issepara.0h5v.s5.40668a780e64 from=seed src=0 shape=ed21faf9 vocab=efcf0eb3
-/
lemma IsSeparated.of_comp [IsSeparated (f ≫ g)] : IsSeparated f := by
  have : IsClosedImmersion (pullback.diagonal (f ≫ g)) := inferInstance
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

variable {f g} in
/--
@isnad1 id=iff.0h5v.s5.641d46f098d0 from=seed src=0 shape=daa213a1 vocab=efcf0eb3
-/
lemma IsSeparated.comp_iff [IsSeparated g] : IsSeparated (f ≫ g) ↔ IsSeparated f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

instance : MorphismProperty.HasOfPostcompProperty @IsSeparated ⊤ where
  of_postcomp f g _ _ := .of_comp f g

instance : MorphismProperty.HasOfPostcompProperty @IsAffineHom @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsAffineHom _)

/--
@isnad1 id=isaffine.0h5v.s5.960eff5bc491 from=seed src=0 shape=77972de3 vocab=ad69cb3d
-/
lemma IsAffineHom.of_comp [IsAffineHom (f ≫ g)] [IsSeparated g] :
    IsAffineHom f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

variable {f g} in
/--
@isnad1 id=iff.0h5v.s5.071cc70dd4a8 from=seed src=0 shape=daa213a1 vocab=8045a5b6
-/
lemma IsAffineHom.comp_iff [IsAffineHom g] : IsAffineHom (f ≫ g) ↔ IsAffineHom f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isclosed.0h5v.s6.11d2e72b98ce from=seed src=0 shape=8e353711 vocab=90d346a3
-/
@[stacks 01KM]
instance isClosedImmersion_equalizer_ι_left {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsClosedImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

/--
Suppose `X` is a reduced scheme and that `f g : X ⟶ Y` agree over some separated `Y ⟶ Z`.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.
@isnad1 id=eq.2h8v.s7.a47c06e4c416 from=seed src=0 shape=d0a87cbe vocab=3b15fca4
-/
lemma ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift ι' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective (Y := X) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

/--
@isnad1 id=eq.3h7v.s7.bb64d7b6566f from=seed src=0 shape=f4399426 vocab=4bc69758
-/
lemma ext_of_fromSpecResidueField_eq (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [IsReduced X]
    (S : Set X) (hS' : Dense S)
    (H : ∀ x ∈ S, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g)
    (H' : f ≫ i = g ≫ i) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated i H' (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx ↦ ⟨equalizer.lift _ (H _ hx) default, ?_⟩) hS'⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, Scheme.fromSpecResidueField_apply]

variable (S) in
/--
Suppose `X` is a reduced `S`-scheme and `Y` is a separated `S`-scheme.
For any `S`-morphisms `f g : X ⟶ Y`, `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.
@isnad1 id=eq.1h7v.s7.f32631941696 from=seed src=0 shape=f718f18d vocab=1f8844c9
-/
lemma ext_of_isDominant_of_isSeparated' [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)]
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] {W} (ι : W ⟶ X) [IsDominant ι]
    (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Y ↘ S) (by simp) ι hU

namespace Scheme

/-- A scheme `X` is separated if it is separated over `⊤_ Scheme`. -/
@[mk_iff]
protected class IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)

attribute [instance] IsSeparated.isSeparated_terminal_from

/--
@isnad1 id=iff.0h1v.s5.6badb981ad40 from=seed src=0 shape=9ba82ea0 vocab=4bfee7bc
-/
lemma isSeparated_iff_isClosedImmersion_prod_lift {X : Scheme.{u}} :
    X.IsSeparated ↔ IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [isSeparated_iff, AlgebraicGeometry.isSeparated_iff, iff_iff_eq,
    ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

instance [X.IsSeparated] : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]

instance (priority := 900) {X : Scheme.{u}} [IsAffine X] : X.IsSeparated := ⟨inferInstance⟩

instance (priority := low) {X : Scheme.{u}} [X.IsSeparated] : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated (terminal.from X)

instance (priority := 900) [X.IsSeparated] : IsSeparated f := by
  apply +allowSynthFailures @IsSeparated.of_comp (g := terminal.from Y)
  rw [terminal.comp_from]
  infer_instance

instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g) :=
  MorphismProperty.of_isPullback (isPullback_equalizer_prod f g).flip inferInstance

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=hasaffin.0h0v.s4.6bb9bbe96ed5 from=seed src=0 shape=bbdc4f68 vocab=0dcba81c
-/
instance IsSeparated.hasAffineProperty :
    HasAffineProperty @IsSeparated fun X _ _ _ ↦ X.IsSeparated := by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff, ← terminal.comp_from f, IsSeparated.comp_iff]
  rfl

/--
Suppose `f g : X ⟶ Y` where `X` is a reduced scheme and `Y` is a separated scheme.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.

Also see `ext_of_isDominant_of_isSeparated` for the general version over arbitrary bases.
@isnad1 id=eq.1h6v.s6.4cbaf38c7643 from=seed src=0 shape=c9497608 vocab=aaa8afb2
-/
lemma ext_of_isDominant [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

end AlgebraicGeometry
