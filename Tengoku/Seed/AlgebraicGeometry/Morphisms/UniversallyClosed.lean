/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
public import Tengoku.Seed.Topology.LocalAtTarget

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.
This implies that `f` is topologically proper (`AlgebraicGeometry.Scheme.Hom.isProperMap`).

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
class UniversallyClosed (f : X ⟶ Y) : Prop where
  universally_isClosedMap : universally (topologically @IsClosedMap) f

/--
@isnad1 id=isclosed.0h3v.s7.2df2efc59b23 from=seed src=0 shape=82a81c7a vocab=7243cb01
-/
lemma Scheme.Hom.isClosedMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f := UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd

/--
@isnad1 id=eq.0h0v.s4.4ea7191479f6 from=seed src=0 shape=70cd5167 vocab=5a5b38f7
-/
theorem universallyClosed_eq : @UniversallyClosed = universally (topologically @IsClosedMap) := by
  ext X Y f; rw [universallyClosed_iff]

instance (priority := 900) [IsClosedImmersion f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsClosedImmersion f' :=
    MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isClosedEmbedding.isClosedMap

/--
@isnad1 id=respects.0h0v.s2.742345360833 from=seed src=0 shape=25b03439 vocab=8109aa90
-/
theorem universallyClosed_respectsIso : RespectsIso @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)

/--
@isnad1 id=isstable.0h0v.s2.6079fd48b708 from=seed src=0 shape=25b03439 vocab=3b9fc78c
-/
instance universallyClosed_isStableUnderBaseChange : IsStableUnderBaseChange @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsClosedMap)

/--
@isnad1 id=isstable.0h0v.s2.dbd42d791235 from=seed src=0 shape=0072ad64 vocab=f274e502
-/
instance isClosedMap_isStableUnderComposition :
    IsStableUnderComposition (topologically @IsClosedMap) where
  comp_mem f g hf hg := IsClosedMap.comp (f := f) (g := g) hg hf

/--
@isnad1 id=isstable.0h0v.s2.4e17d757eabd from=seed src=0 shape=25b03439 vocab=b047e241
-/
instance universallyClosed_isStableUnderComposition :
    IsStableUnderComposition @UniversallyClosed := by
  rw [universallyClosed_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=universa.0h5v.s5.c5ac82dc33dc from=seed src=0 shape=2758f569 vocab=f9761aa2
-/
lemma UniversallyClosed.of_comp_surjective {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Surjective f] : UniversallyClosed g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have := UniversallyClosed.universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsClosedMap.of_comp_surjective (MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›).1
    (Scheme.Hom.continuous _) this

/--
@isnad1 id=universa.0h5v.s5.b038125faf69 from=seed src=0 shape=73d4a103 vocab=a0cab4f4
-/
instance universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g) :=
  comp_mem _ _ _ hf hg

instance : MorphismProperty.IsMultiplicative @UniversallyClosed where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=universa.0h5v.s5.4cfee056ca55 from=seed src=0 shape=549492a1 vocab=7684ccd5
-/
instance universallyClosed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=universa.0h5v.s5.b7f267d2e871 from=seed src=0 shape=7386bcd0 vocab=8f424cdc
-/
instance universallyClosed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/--
@isnad1 id=iszarisk.0h0v.s1.0510ea569830 from=seed src=0 shape=49959d42 vocab=c2894fd5
-/
instance universallyClosed_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isClosedMap_iff_restrictPreimage.mpr H

instance (f : X ⟶ Y) (V : Y.Opens) [UniversallyClosed f] : UniversallyClosed (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

open Scheme.Pullback _root_.PrimeSpectrum MvPolynomial in
/-- If `X` is universally closed over a field, then `X` is quasi-compact.
@isnad1 id=compacts.0h3v.s5.e0df49967e0d from=seed src=0 shape=99e73c5d vocab=64f6db4d
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let Z : Set (pullback f q :) := (⨆ i, fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i) : (pullback f q).Opens)ᶜ
  have hZ : IsClosed Z := by
    simp only [Z, isClosed_compl_iff, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    exact isOpen_iUnion fun i ↦ (fT.continuous.1 _ (Ti i).2).inter (p.continuous.1 _ (U i).2)
  let Zc : T.Opens := ⟨(fT '' Z)ᶜ, (fT.isClosedMap _ hZ).isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.I₀ K →ₐ[K] K := MvPolynomial.aeval (fun _ ↦ 1)
  let t : T := Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht (i : 𝒰.I₀) : t ∈ Ti i := show ψ (.X i) ≠ 0 by simp [ψ]
  have htZc : t ∈ Zc := by
    intro ⟨z, hz, hzt⟩
    suffices ∃ i, fT z ∈ Ti i ∧ p z ∈ U i from hz (by simpa)
    exact ⟨𝒰.idx (p z), hzt ▸ ht _, by simpa [U] using 𝒰.covers (p z)⟩
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ := Opens.isBasis_iff_nbhd.mp isBasis_basic_opens htZc
  let σ : Finset 𝒰.I₀ := MvPolynomial.vars g
  let φ : MvPolynomial 𝒰.I₀ K →+* MvPolynomial 𝒰.I₀ K :=
    (MvPolynomial.aeval fun i : 𝒰.I₀ ↦ if i ∈ σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := Spec.map (CommRingCat.ofHom φ) t
  have ht'g : t' ∈ PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htU'
  have h : t' ∉ fT '' Z := hU'le ht'g
  suffices ⋃ i ∈ σ, (U i).1 = Set.univ from
    ⟨this ▸ Finset.isCompact_biUnion _ fun i _ ↦ isCompact_range (𝒰.f i).continuous⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, rfl, hzr⟩ := exists_preimage_pullback x t' (Subsingleton.elim (f x) (q t'))
  suffices ∀ i, t ∈ (Ti i).comap ⟨_, continuous_comap φ⟩ → p z ∉ U i from
    ⟨z, by simpa [Z, p, fT, hzr], hzr⟩
  intro i hi₁ hi₂
  rw [comap_basicOpen, show φ (.X i) = 0 by simpa [φ] using (hx i · hi₂), basicOpen_zero] at hi₁
  cases hi₁

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isproper.0h3v.s7.5a9829ed1bcd from=seed src=0 shape=82a81c7a vocab=e0f9b2f7
-/
@[stacks 04XU]
lemma Scheme.Hom.isProperMap (f : X ⟶ Y) [UniversallyClosed f] : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f.continuous, f.isClosedMap, fun y ↦ ?_⟩
  have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
  rw [← Scheme.range_fromSpecResidueField, ← Scheme.Pullback.range_fst]
  exact isCompact_range (Scheme.Hom.continuous _)

instance (priority := 900) [UniversallyClosed f] : QuasiCompact f where
  isCompact_preimage _ _ := f.isProperMap.isCompact_preimage

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h0v.s6.4c0c71f36ae2 from=seed src=0 shape=443178b9 vocab=85d90799
-/
lemma universallyClosed_eq_universallySpecializing :
    @UniversallyClosed = (topologically @SpecializingMap).universally ⊓ @QuasiCompact := by
  rw [← universally_eq_iff (P := @QuasiCompact).mpr inferInstance, ← universally_inf]
  apply le_antisymm
  · rw [← universally_eq_iff (P := @UniversallyClosed).mpr inferInstance]
    exact universally_mono fun X Y f H ↦ ⟨f.isClosedMap.specializingMap, inferInstance⟩
  · rw [universallyClosed_eq]
    exact universally_mono fun X Y f ⟨h₁, h₂⟩ ↦ (isClosedMap_iff_specializingMap _).mpr h₁

/--
@isnad1 id=surjecti.0h3v.s4.19ecbc0d8bfc from=seed src=0 shape=d492d1ea vocab=9b719cd3
-/
instance (priority := low) Surjective.of_universallyClosed_of_isDominant
    [UniversallyClosed f] [IsDominant f] : Surjective f := by
  rw [surjective_iff, ← Set.range_eq_univ, ← f.denseRange.closure_range,
    f.isClosedMap.isClosed_range.closure_eq]

end AlgebraicGeometry
