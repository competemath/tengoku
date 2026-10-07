/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.Ring.Small
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.RingHomProperties
public import Tengoku.Seed.CategoryTheory.MorphismProperty.Comma
public import Tengoku.Seed.RingTheory.RingHom.EssFiniteType
public import Tengoku.Seed.RingTheory.RingHom.FiniteType
public import Tengoku.Seed.RingTheory.Spectrum.Prime.Jacobson

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions and base change.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FiniteType

/--
@isnad1 id=finitety.3h5v.s9.0825e2cade21 from=seed src=0 shape=3953db45 vocab=8c931efd
-/
alias Scheme.Hom.finiteType_appLE := LocallyOfFiniteType.finiteType_appLE

instance : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType where
  isLocal_ringHomProperty := RingHom.finiteType_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFiniteType_iff, affineLocally_iff_forall_isAffineOpen]

/--
@isnad1 id=locallyo.0h3v.s4.9982235e1e75 from=seed src=0 shape=892cb9de vocab=d69576df
-/
instance (priority := 900) locallyOfFiniteType_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finiteType_holdsForLocalizationAway.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @LocallyOfFiniteType :=
  HasRingHomProperty.stableUnderComposition RingHom.finiteType_stableUnderComposition

/--
@isnad1 id=locallyo.0h5v.s5.d9621bd40eaa from=seed src=0 shape=73d4a103 vocab=9d649f3b
-/
instance locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/--
@isnad1 id=locallyo.0h5v.s5.bc6ba22e62d6 from=seed src=0 shape=ed21faf9 vocab=9d649f3b
-/
theorem locallyOfFiniteType_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.FiniteType.of_comp_finiteType) ‹_›

instance : MorphismProperty.IsMultiplicative @LocallyOfFiniteType where
  id_mem _ := inferInstance

open scoped TensorProduct in
/--
@isnad1 id=isstable.0h0v.s2.a5a001fccd81 from=seed src=0 shape=25b03439 vocab=fb8a2dec
-/
instance locallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finiteType_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [LocallyOfFiniteType f] : LocallyOfFiniteType (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/--
@isnad1 id=essfinit.0h4v.s9.18316042350b from=seed src=0 shape=f861e1e1 vocab=f6b0f5f1
-/
lemma LocallyOfFiniteType.stalkMap [LocallyOfFiniteType f] (x : X) :
    (f.stalkMap x).hom.EssFiniteType :=
  HasRingHomProperty.stalkMap_of_respectsIso RingHom.EssFiniteType.respectsIso
    (fun f hf _ _ ↦ RingHom.EssFiniteType.holdsForLocalization.localRingHom
      RingHom.EssFiniteType.stableUnderComposition
      RingHom.EssFiniteType.isStableUnderBaseChange.localizationPreserves _
      (RingHom.FiniteType.essFiniteType hf)) ‹_› x

instance {R} [CommRing R] [IsJacobsonRing R] : JacobsonSpace <| Spec <| .of R :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

instance {R : CommRingCat} [IsJacobsonRing R] : JacobsonSpace (Spec R) :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=jacobson.0h3v.s5.77af1423fbc7 from=seed src=0 shape=5602b55b vocab=eac26f4f
-/
nonrec lemma LocallyOfFiniteType.jacobsonSpace
    (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace Y] : JacobsonSpace X := by
  wlog hY : ∃ S, Y = Spec S
  · rw [(Scheme.OpenCover.isOpenCover_opensRange (Y.affineCover.pullback₁ f)).jacobsonSpace_iff]
    intro i
    have inst : LocallyOfFiniteType (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : JacobsonSpace Y := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    have inst : JacobsonSpace (Y.affineCover.X i) :=
      .of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    let e := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.isEmbedding.toHomeomorph
    have := this (Y.affineCover.pullbackHom f i) ⟨_, rfl⟩
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : JacobsonSpace (Spec R) := ‹_› -- TC gets stuck on the WLOG hypothesis without it.
    rw [X.affineCover.isOpenCover_opensRange.jacobsonSpace_iff]
    intro i
    have := this _ (X.affineCover.f i ≫ f) ⟨_, rfl⟩
    let e := (X.affineCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph
    exact .of_isClosedEmbedding e.symm.isClosedEmbedding
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  have : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp (isJacobsonRing_of_finiteType (A := R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The category of affine schemes locally of finite type over a fixed base scheme is essentially small.
TODO: extend this to (relatively) quasi-compact schemes.
@isnad1 id=essentia.1h2v.s7.48da169245ab from=seed src=0 shape=ae513393 vocab=2f45a226
-/
lemma essentiallySmall_costructuredArrow_Spec
    (P : MorphismProperty Scheme.{u}) (hP : P ≤ @LocallyOfFiniteType) [P.RespectsIso] :
    EssentiallySmall.{u} (P.CostructuredArrow ⊤ Scheme.Spec X) := by
  let F := MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec X ⋙ CostructuredArrow.proj _ _
  refine .of_functor F ?_ ?_
  · let Q' : ObjectProperty CommRingCat.{u} := fun S ↦
      ∃ R, (R ∈ Set.range fun U ↦ Γ(X, U)) ∧ ∃ (f : R ⟶ S), f.hom.FiniteType
    have : Q'.EssentiallySmall := CommRingCat.essentiallySmall_of_finiteType fun S ↦ id
    suffices ObjectProperty.EssentiallySmall.{u} (· ∈ Set.range (Opposite.unop ∘ F.obj)) by
      rw [← ObjectProperty.essentiallySmall_unop_iff]
      refine .of_le (Q := .isoClosure (· ∈ Set.range (Opposite.unop ∘ F.obj))) ?_
      exact fun R ⟨S, e⟩ ↦ ⟨_, ⟨S, rfl⟩, ⟨e.some.unop⟩⟩
    refine CommRingCat.essentiallySmall_of_localizationAway (Q := Q'.isoClosure) ?_
    rintro _ ⟨S, rfl⟩
    have (q : Spec (F.obj S).unop) : ∃ f, q ∈ PrimeSpectrum.basicOpen f ∧
        Q' Γ(Spec (F.obj S).unop, PrimeSpectrum.basicOpen f) := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ <| S.hom q) isOpen_univ
      obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hqf, hfU⟩ :=
        PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hqU (S.hom ⁻¹ᵁ U).isOpen
      have : LocallyOfFiniteType S.hom := hP _ S.prop
      exact ⟨f, hqf, _, ⟨U, rfl⟩, S.hom.appLE _ _ hfU,
        (S.hom.finiteType_appLE hU (.Spec_basicOpen _)) _⟩
    choose f hqf hf using this
    refine ⟨Set.range f, PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp ?_, Set.forall_mem_range.mpr ?_⟩
    · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hqf _⟩
    · dsimp
      exact fun q ↦ ⟨_, hf q, ⟨(IsLocalization.algEquiv (.powers (f q)) _
        ((Spec.structureSheaf _).obj.obj (op _))).toRingEquiv.toCommRingCatIso⟩⟩
  · intro R
    refine ⟨.ofObj fun f : { f : Spec R.unop ⟶ X // P f } ↦ .mk _ f.1 f.2, inferInstance, ?_⟩
    refine fun S ⟨e⟩ ↦ ⟨_, .mk ⟨Spec.map e.inv.unop ≫ S.hom, ?_⟩,
      ⟨MorphismProperty.CostructuredArrow.isoMk e trivial trivial ?_⟩⟩
    · simp [← Spec.map_comp_assoc, F]
    · exact (P.cancel_left_of_respectsIso _ _).mpr S.prop

end AlgebraicGeometry
