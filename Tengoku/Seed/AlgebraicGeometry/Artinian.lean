/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Noetherian
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Immersion
public import Tengoku.Seed.RingTheory.HopkinsLevitzki

/-!
# Artinian and Locally Artinian Schemes

We define and prove basic properties about Artinian and locally Artinian Schemes.

## Main definitions

* `AlgebraicGeometry.IsLocallyArtinian`: A scheme is locally Artinian if for all open affines,
  the section ring is an Artinian ring.

* `AlgebraicGeometry.IsArtinianScheme`: A scheme is Artinian if it is locally Artinian and
  quasi-compact.

## Main results

* `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`: A scheme is
  locally Artinian if and only if it is LocallyNoetherian and it has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology`: A scheme is Artinian
  if and only if it is Noetherian and has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.finite`: An Artinian scheme is finite.

* `AlgebraicGeometry.Scheme.isArtinianScheme_Spec`: A commutative ring R is Artinian if and only if
  Spec R is Artinian.

-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A scheme `X` is locally Artinian if `𝒪ₓ(U)` is Artinian for all affine `U`. -/
class IsLocallyArtinian (X : Scheme) : Prop where
  isArtinianRing_presheaf_obj : ∀ (U : X.affineOpens),
    IsArtinianRing Γ(X, U) := by infer_instance

attribute [instance] IsLocallyArtinian.isArtinianRing_presheaf_obj

/--
@isnad1 id=islocall.0h1v.s2.c5c5400033e7 from=seed src=0 shape=6321fd23 vocab=5cc89774
-/
instance IsLocallyArtinian.isLocallyNoetherian [h : IsLocallyArtinian X] :
    IsLocallyNoetherian X where

/--
@isnad1 id=isartini.0h1v.s9.abe601f0ad06 from=seed src=0 shape=a62eb39e vocab=6d118e81
-/
instance IsLocallyArtinian.isArtinianRing_of_isAffine [h : IsLocallyArtinian X] [IsAffine X] :
    IsArtinianRing Γ(X, ⊤) :=
  h.1 ⟨⊤, isAffineOpen_top X⟩

/--
@isnad1 id=islocall.1h1v.s5.1e11cb57162e from=seed src=0 shape=fe490892 vocab=b0cd3446
-/
lemma IsLocallyArtinian.of_topologicalKrullDim_le_zero
    [IsLocallyNoetherian X] (h : topologicalKrullDim X ≤ 0) : IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U := by
    have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim,
      Nat.cast_zero, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
    change topologicalKrullDim (Spec Γ(X, U)) ≤ 0
    rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X U).trans h

/--
@isnad1 id=islocall.0h1v.s4.282cb6565ecd from=seed src=0 shape=b5bf1bb4 vocab=3d188fd4
-/
theorem IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
    [IsLocallyNoetherian X] [DiscreteTopology X] :
    IsLocallyArtinian X :=
  .of_topologicalKrullDim_le_zero (topologicalKrullDim_zero_of_discreteTopology X)

/-- See `isLocallyArtinian_of_isImmersion`. -/
private lemma IsLocallyArtinian.of_isOpenImmersion [IsOpenImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U :=
    have : IsArtinianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, U.2.image_of_isOpenImmersion f⟩
    (f.appIso U).commRingCatIsoToRingEquiv.surjective.isArtinianRing

instance [IsLocallyArtinian X] {U : X.Opens} : IsLocallyArtinian U := .of_isOpenImmersion U.ι

instance [IsLocallyArtinian X] {U : X.OpenCover} (i) : IsLocallyArtinian (U.X i) :=
  .of_isOpenImmersion (U.f i)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=discrete.0h1v.s4.212ecaaf50bd from=seed src=0 shape=7c9df8e0 vocab=08a64fe4
-/
instance (priority := low) IsLocallyArtinian.discreteTopology [IsLocallyArtinian X] :
    DiscreteTopology X := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  obtain ⟨W, hW1, hW2, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have : IsArtinianRing Γ(X, W) := IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hW1⟩
  have : DiscreteTopology (Spec Γ(X, W)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  have : DiscreteTopology W := hW1.isoSpec.hom.homeomorph.symm.discreteTopology
  simpa using (isOpen_discrete ({⟨x, hW2⟩} : Set W)).trans W.2

/--
@isnad1 id=iff.0h1v.s4.8802fdf5219c from=seed src=0 shape=9ab1bf84 vocab=3d188fd4
-/
theorem IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology :
    IsLocallyArtinian X ↔ IsLocallyNoetherian X ∧ DiscreteTopology X :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ .of_isLocallyNoetherian_of_discreteTopology⟩

-- This can be extended to locally quasi-finite morphisms.
/--
@isnad1 id=islocall.0h3v.s4.87b4a7b0450d from=seed src=0 shape=9715b773 vocab=7d48236a
-/
theorem IsLocallyArtinian.of_isImmersion [IsImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X :=
  iff_isLocallyNoetherian_and_discreteTopology.mpr
    ⟨LocallyOfFiniteType.isLocallyNoetherian f, f.isEmbedding.discreteTopology⟩

/-- A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme.
@isnad1 id=iff.0h1v.s4.eacfa28ceb30 from=seed src=0 shape=7072e12b vocab=609ce589
-/
@[simp] theorem Scheme.isLocallyArtinianScheme_Spec {R : CommRingCat} :
    IsLocallyArtinian (Spec R) ↔ IsArtinianRing R where
  mp _ := (AlgebraicGeometry.Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.isArtinianRing
  mpr _ := .of_topologicalKrullDim_le_zero
    (topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum _))

/--
@isnad1 id=iff.0h2v.s5.298f474f80e6 from=seed src=0 shape=9de9a46e vocab=a279c36d
-/
theorem isLocallyArtinian_iff_openCover (𝒰 : X.OpenCover) :
    IsLocallyArtinian X ↔ ∀ (i : 𝒰.I₀), IsLocallyArtinian (𝒰.X i) := by
  refine ⟨fun h ↦ inferInstance, fun H ↦ ?_⟩
  refine IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mpr ⟨?_, ?_⟩
  · exact (isLocallyNoetherian_iff_openCover 𝒰).mpr inferInstance
  · refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    simpa using (𝒰.f i).isOpenEmbedding.isOpenMap _ (isOpen_discrete {x})

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iff.2h3v.s9.e1c347708c11 from=seed src=0 shape=d5ea5a6c vocab=a98ff8ad
-/
theorem isLocallyArtinian_iff_of_isOpenCover {ι : Type*} {U : ι → X.Opens}
    (hU : TopologicalSpace.IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    IsLocallyArtinian X ↔ ∀ i, IsArtinianRing Γ(X, U i) := by
  refine ⟨fun _ _ ↦ IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU' _⟩, fun H ↦ ?_⟩
  rw [isLocallyArtinian_iff_openCover (X.openCoverOfIsOpenCover U hU)]
  have : ∀ i, IsLocallyArtinian (Spec Γ(X, U i)) := by simpa
  exact fun i ↦ .of_isImmersion (hU' _).isoSpec.hom

instance (priority := low) {X : Scheme} [IsEmpty X] : IsLocallyArtinian X where

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := low) {X : Scheme} [DiscreteTopology X] [IsReduced X] :
    IsLocallyArtinian X := by
  wlog hX : Subsingleton X generalizing X
  · let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover
      (fun x : X ↦ ⟨{x}, isOpen_discrete _⟩) (.mk (by ext; simp))
    have inst (i : _) : DiscreteTopology (𝒰.X i) := (𝒰.f i).isOpenEmbedding.discreteTopology
    have inst (i : _) : IsReduced (𝒰.X i) := isReduced_of_isOpenImmersion (𝒰.f i)
    exact (isLocallyArtinian_iff_openCover 𝒰).mpr
      fun i ↦ this (inferInstanceAs (Subsingleton ({i} : Set X)))
  cases isEmpty_or_nonempty X
  · infer_instance
  have : IsIntegral X := (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
    ⟨⟨inferInstance⟩, inferInstance⟩
  let := (isField_of_isIntegral_of_subsingleton X).toField
  have : IsLocallyArtinian (Spec Γ(X, ⊤)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact .of_isImmersion X.isoSpec.hom

/-- A scheme is Artinian if it is locally Artinian and quasi-compact -/
@[mk_iff]
class IsArtinianScheme (X : Scheme.{u}) : Prop extends IsLocallyArtinian X, CompactSpace X

/-- The underlying type of an Artinian Scheme is finite
@isnad1 id=finite.0h1v.s4.5a09f3eeb8f8 from=seed src=0 shape=7c9df8e0 vocab=c251aac6
-/
instance (priority := low) IsArtinianScheme.finite [IsArtinianScheme X] :
    Finite X := finite_of_compact_of_discrete

/--
@isnad1 id=isnoethe.0h1v.s2.9f4319f697b9 from=seed src=0 shape=6321fd23 vocab=deea5634
-/
instance (priority := low) IsArtinianScheme.isNoetherianScheme [IsArtinianScheme X] :
    IsNoetherian X where

/-- A scheme is Artinian if and only if it is Noetherian and has the discrete topology.
@isnad1 id=iff.0h1v.s4.a0c64c0b9010 from=seed src=0 shape=9ab1bf84 vocab=ccbc3aa0
-/
theorem IsArtinianScheme.iff_isNoetherian_and_discreteTopology :
    IsArtinianScheme X ↔ IsNoetherian X ∧ DiscreteTopology X := by
  aesop (add simp [isArtinianScheme_iff, isNoetherian_iff,
    IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology])

instance {R : CommRingCat} [IsArtinianRing R] :
    IsArtinianScheme (Spec R) :=
  IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mpr
    ⟨inferInstance, inferInstanceAs (DiscreteTopology (PrimeSpectrum R))⟩

/-- Spec of a field is artinian. -/
instance (priority := low) {X : Scheme} [Subsingleton X] [IsReduced X] :
    IsArtinianScheme X where

/-- A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme
@isnad1 id=iff.0h1v.s4.ccf597c6903b from=seed src=0 shape=7072e12b vocab=5370f458
-/
theorem Scheme.isArtinianScheme_Spec {R : CommRingCat} :
    IsArtinianScheme (Spec R) ↔ IsArtinianRing R := by
  simp [isArtinianScheme_iff, (inferInstance : CompactSpace (Spec R))]

end AlgebraicGeometry
