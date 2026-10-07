/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Integral
public import Tengoku.Seed.Algebra.Category.Ring.Epi
public import Tengoku.Seed.RingTheory.Finiteness.Prod
public import Tengoku.Seed.RingTheory.RingHom.Finite

/-!

# Finite morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is finite if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is finite.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is finite.

Also see `AlgebraicGeometry.IsFinite.finite_preimage_singleton` in
`Mathlib/AlgebraicGeometry/Fiber.lean` for the fact that finite morphisms have finite fibers.

-/

public section

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
class IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  finite_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.Finite

/--
@isnad1 id=finite.1h4v.s10.5f9376ea2685 from=seed src=0 shape=048d87f5 vocab=4d634090
-/
alias Scheme.Hom.finite_app := IsFinite.finite_app

namespace IsFinite

set_option backward.isDefEq.respectTransparency.types false in
instance : HasAffineProperty @IsFinite
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom) := by
  change HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

set_option backward.isDefEq.respectTransparency.types false in
instance : IsStableUnderComposition @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderComposition inferInstance
    RingHom.finite_stableUnderComposition

set_option backward.isDefEq.respectTransparency.types false in
instance : IsStableUnderBaseChange @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange inferInstance
    RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
instance : ContainsIdentities @IsFinite :=
  HasAffineProperty.affineAnd_containsIdentities inferInstance
    RingHom.finite_respectsIso RingHom.finite_containsIdentities

instance : IsMultiplicative @IsFinite where

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iff.0h3v.s5.295bfd8aee7f from=seed src=0 shape=110effa8 vocab=040b3399
-/
@[simp]
lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsFinite (Spec.map f) ↔ f.hom.Finite := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite), and_iff_right (by infer_instance),
    RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := 900) [IsIso f] : IsFinite f := of_isIso @IsFinite f

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g ‹IsFinite f› ‹IsFinite g›

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite g] : IsFinite (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite f] : IsFinite (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [IsFinite f] : IsFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iff.0h3v.s4.c6f5d393003c from=seed src=0 shape=2caf7a2f vocab=5e54b830
-/
lemma iff_isIntegralHom_and_locallyOfFiniteType :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite),
    HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom),
    RingHom.finite_iff_isIntegral_and_finiteType, ← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ ↦
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).symm

lemma eq_inf :
    @IsFinite = (@IsIntegralHom ⊓ @LocallyOfFiniteType : MorphismProperty Scheme) := by
  ext; exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _

instance (priority := 900) [IsFinite f] : IsIntegralHom f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).1

instance (priority := 900) [IsFinite f] : LocallyOfFiniteType f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).2

set_option backward.isDefEq.respectTransparency false in
lemma _root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f := by
  wlog hY : IsAffine Y
  · rw [← monomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := monomorphisms _) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion),
    HasAffineProperty.iff_of_isAffine (P := @IsFinite),
    RingHom.surjective_iff_epi_and_finite, @and_comm (Epi _), ← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ ↦
    Iff.trans ?_ (arrow_mk_iso_iff (monomorphisms _) (arrowIsoSpecΓOfIsAffine f).symm)
  trans Mono (f.app ⊤).op
  · exact ⟨fun h ↦ inferInstance, fun h ↦ show Epi (f.app ⊤).op.unop by infer_instance⟩
  exact (Functor.mono_map_iff_mono Scheme.Spec _).symm

lemma _root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono :
    @IsClosedImmersion = (@IsFinite ⊓ monomorphisms Scheme : MorphismProperty _) := by
  ext; exact IsClosedImmersion.iff_isFinite_and_mono _

instance (priority := 900) (f : X ⟶ Y) [IsClosedImmersion f] : IsFinite f :=
  ((IsClosedImmersion.iff_isFinite_and_mono f).mp ‹_›).1

instance : MorphismProperty.HasOfPostcompProperty @IsFinite @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsFinite _)

/--
@isnad1 id=isfinite.0h5v.s5.07d7cd0072cc from=seed src=0 shape=77972de3 vocab=089c73d3
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite (f ≫ g)] [IsSeparated g] :
    IsFinite f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/--
@isnad1 id=iff.0h5v.s5.9ce470bb5449 from=seed src=0 shape=daa213a1 vocab=43488255
-/
lemma comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsFinite g] :
    IsFinite (f ≫ g) ↔ IsFinite f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsFinite f] [IsFinite g] :
    IsFinite (Limits.coprod.desc f g) := by
  refine HasAffineProperty.coprodDesc_affineAnd inferInstance RingHom.finite_respectsIso
    ?_ _ _ ‹_› ‹_›
  intros R S T _ _ _ f g _ _
  algebraize [f, g]
  refine RingHom.finite_algebraMap.mpr inferInstance

end IsFinite

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=finite.0h3v.s10.8d09a9391d25 from=seed src=0 shape=57976d81 vocab=63bf2792
-/
lemma Scheme.Hom.finite_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsFinite f] :
    f.appTop.hom.Finite :=
  (HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X` is a Jacobson scheme and `k` is a field,
`Spec(k) ⟶ X` is finite iff it is (locally) of finite type.
(The statement is more general to allow the empty scheme as well)
@isnad1 id=iff.0h3v.s5.ce183527e1d7 from=seed src=0 shape=32c223c7 vocab=310bdd4e
-/
lemma isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Subsingleton X] [IsReduced X] [JacobsonSpace Y] :
    IsFinite f ↔ LocallyOfFiniteType f := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    have inst (i) := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.injective.subsingleton
    have inst (i) := isReduced_of_isOpenImmersion ((Y.affineCover.pullback₁ f).f i)
    have inst (i) := JacobsonSpace.of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    exact forall_congr' fun i ↦ this ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ R, X = Spec R generalizing X
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) X.isoSpec.inv,
      ← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) X.isoSpec.inv]
    have inst := X.isoSpec.inv.isOpenEmbedding.injective.subsingleton
    refine this ⟨_, rfl⟩
  cases isEmpty_or_nonempty X
  · exact ⟨inferInstance, inferInstance⟩
  have : IrreducibleSpace X := ⟨‹_›⟩
  obtain ⟨R, rfl⟩ := hX
  have : IsDomain R := (affine_isIntegral_iff R).mp (isIntegral_of_irreducibleSpace_of_isReduced _)
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [IsFinite.SpecMap_iff, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := (PrimeSpectrum.t1Space_iff_isField (R := R)).mp (show T1Space (Spec R) by infer_instance)
  let := this.toField
  let := φ.hom.toAlgebra
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  change Module.Finite _ _ ↔ Algebra.FiniteType _ _
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ finite_of_finite_type_of_isJacobsonRing _ _⟩

/--
@isnad1 id=le.0h3v.s8.56d66e0bee77 from=seed src=0 shape=f4efe938 vocab=65357d7c
-/
@[stacks 01TB "(1) => (3)"]
lemma Scheme.Hom.closePoints_subset_preimage_closedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [JacobsonSpace Y] [LocallyOfFiniteType f] :
    closedPoints X ⊆ f ⁻¹' closedPoints Y := by
  intro x hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  simpa [Set.range_comp, Scheme.range_fromSpecResidueField] using
    (X.fromSpecResidueField x ≫ f).isClosedMap.isClosed_range

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iff.0h2v.s6.ce6e4006b82f from=seed src=0 shape=a8267977 vocab=768afdf6
-/
@[stacks 01TB "(1) => (2)"]
lemma isClosed_singleton_iff_locallyOfFiniteType {X : Scheme.{u}} [JacobsonSpace X] {x : X} :
    IsClosed {x} ↔ LocallyOfFiniteType (X.fromSpecResidueField x) := by
  constructor
  · exact fun H ↦ have := isClosed_singleton_iff_isClosedImmersion.mp H; inferInstance
  · intro H
    simpa using (X.fromSpecResidueField x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint _)

end AlgebraicGeometry
