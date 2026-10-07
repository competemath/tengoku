/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Justus Springer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
public import Tengoku.Seed.RingTheory.RingHom.PurelyInseparable
public import Tengoku.Seed.Topology.LocalAtTarget

/-!
# Universally injective morphism

A morphism of schemes `f : X ⟶ Y` is universally injective if `X ×[Y] Y' ⟶ Y'` is injective
for all base changes `Y' ⟶ Y`. This is equivalent to the diagonal morphism being surjective
(`AlgebraicGeometry.UniversallyInjective.iff_diagonal`).

We show that being universally injective is local at the target, and is stable under
compositions and base changes.

We also prove that universally injective is equivalent to being injective with
purely inseparable residue field extensions (also known as a radical morphism), see
`AlgebraicGeometry.tfae_universallyInjective` and Stacks tag 01S4.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty Function

/--
A morphism of schemes `f : X ⟶ Y` is universally injective if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is injective (on points).
-/
@[mk_iff]
class UniversallyInjective (f : X ⟶ Y) : Prop where
  universally_injective : universally (topologically (Injective ·)) f

/--
@isnad1 id=injectiv.0h3v.s7.486ac643f66c from=seed src=0 shape=82a81c7a vocab=02321681
-/
theorem Scheme.Hom.injective (f : X ⟶ Y) [UniversallyInjective f] :
    Function.Injective f :=
  UniversallyInjective.universally_injective _ _ _ .of_id_snd

/--
@isnad1 id=eq.0h0v.s5.16accc923ca8 from=seed src=0 shape=7ba36866 vocab=2fb78cf7
-/
theorem universallyInjective_eq :
    @UniversallyInjective = universally (topologically (Injective ·)) := by
  ext X Y f; rw [universallyInjective_iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h0v.s4.2fe1aa6d7cbe from=seed src=0 shape=d9c52ade vocab=cf0d3085
-/
theorem universallyInjective_eq_diagonal :
    @UniversallyInjective = diagonal @Surjective := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x ↦ ⟨pullback.fst f f x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstance : IsStableUnderBaseChange (diagonal @Surjective)),
      universallyInjective_eq]
    apply universally_mono
    intro X Y f hf x₁ x₂ e
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    obtain ⟨t, rfl⟩ := hf.1 t
    rw [← ht₁, ← ht₂, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst,
      pullback.diagonal_snd]

/--
@isnad1 id=iff.0h3v.s5.d94e3f9fd585 from=seed src=0 shape=40728932 vocab=0af2b98b
-/
theorem UniversallyInjective.iff_diagonal :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) := by
  rw [universallyInjective_eq_diagonal]; rfl

instance (priority := 900) [Mono f] : UniversallyInjective f :=
  have := (pullback.isIso_diagonal_iff f).mpr inferInstance
  (UniversallyInjective.iff_diagonal f).mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=respects.0h0v.s2.79ce18f84663 from=seed src=0 shape=25b03439 vocab=501a2de1
-/
theorem UniversallyInjective.respectsIso : RespectsIso @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=isstable.0h0v.s2.02eb0a4f6e20 from=seed src=0 shape=25b03439 vocab=4d97fbe4
-/
instance UniversallyInjective.isStableUnderBaseChange :
    IsStableUnderBaseChange @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

/--
@isnad1 id=isstable.0h0v.s2.41dc350301c8 from=seed src=0 shape=25b03439 vocab=7f466053
-/
instance universallyInjective_isStableUnderComposition :
    IsStableUnderComposition @UniversallyInjective :=
  universallyInjective_eq ▸ inferInstance

instance : MorphismProperty.IsMultiplicative @UniversallyInjective where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iszarisk.0h0v.s1.b26e3474f795 from=seed src=0 shape=49959d42 vocab=b91bc22a
-/
instance universallyInjective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=tfae.0h3v.s9.92cfd41a24fd from=seed src=0 shape=20abfd89 vocab=05cf944e
-/
@[stacks 01S4]
theorem tfae_universallyInjective :
    List.TFAE [
      UniversallyInjective f,
      ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f),
      Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable,
      Surjective (pullback.diagonal f) ] := by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 → 2 := by
    intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
    obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr((Y.SpecToEquivOfField K) $(hg))
    apply (X.SpecToEquivOfField K).injective
    dsimp at e h
    simp only [Scheme.descResidueField_stalkClosedPointTo_comp] at e h
    rw [← f.residueFieldMap_congr'_assoc (h_inj e), CommRingCat.hom_ext_iff] at h
    rw [Scheme.SpecToEquivOfField_eq_iff]
    let x := g₁ (IsLocalRing.closedPoint K)
    have hfx := hf x
    algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
    refine ⟨h_inj e, CommRingCat.hom_ext ?_⟩
    exact IsPurelyInseparable.injective_comp_algebraMap
      (Y.residueField (f x)) (X.residueField x) _ h
  tfae_have 2 → 4 := fun h ↦ by
    rw [surjective_iff]
    intro z
    let φ := (pullback f f).fromSpecResidueField z
    have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
      h ((pullback f f).residueField z) (by simp [pullback.condition])
    have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by cat_disch
    refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.fromSpecResidueField_apply]
  tfae_have 4 → 3 := fun hf ↦ by
    have := tfae_1_iff_4.mpr hf
    refine ⟨f.injective, ?_⟩
    rw [surjective_iff] at hf
    intro x
    algebraize [(f.residueFieldMap x).hom]
    rw [RingHom.IsPurelyInseparable, isPurelyInseparable_iff_subsingleton_emb, subsingleton_iff]
    intro σ₁ σ₂
    apply AlgHom.coe_ringHom_injective
    let g₁ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₁.toRingHom⟩
    let g₂ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₂.toRingHom⟩
    suffices X.SpecToEquivOfField _ g₁ = X.SpecToEquivOfField _ g₂ by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact congr($(this).2.hom)
    let q := pullback.lift (f := f) (g := f) g₁ g₂ <| by
      simp only [g₁, g₂, Scheme.SpecToEquivOfField_symm_apply, AlgHom.toRingHom_eq_coe,
        Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
      congr 2
      ext a
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact (AlgHom.commutes σ₁ a).trans (AlgHom.commutes σ₂ a).symm
    have q_fst : q ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
    have q_snd : q ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
    rw [Scheme.SpecToEquivOfField_eq_iff, ← q_fst, ← q_snd]
    obtain ⟨u, hu⟩ := hf (q (IsLocalRing.closedPoint _))
    have hux : u = x := by
      have := congr(pullback.fst f f $(hu))
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at this
      simpa [Scheme.SpecToEquivOfField_symm_apply, q_fst, g₁] using this
    refine ⟨by simp [g₁, g₂, q_fst, q_snd], ?_⟩
    dsimp
    simp only [Scheme.descResidueField_stalkClosedPointTo_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.residueFieldCongr (hux ▸ hu).symm).hom]
    have : Mono (Scheme.Hom.residueFieldMap (pullback.diagonal f) x) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    simp [← cancel_mono ((pullback.diagonal f).residueFieldMap x), ← Scheme.residueFieldMap_comp,
      (pullback.fst f f).residueFieldMap_congr', (pullback.snd f f).residueFieldMap_congr'_assoc,
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd f),
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst f)]
  tfae_finish

end AlgebraicGeometry
