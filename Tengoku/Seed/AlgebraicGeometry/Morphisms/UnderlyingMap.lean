/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.LocalAtTarget
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Constructors

/-!
# Properties on the underlying functions of morphisms of schemes

This file includes various results on properties of morphisms of schemes that come from properties
of the underlying map of topological spaces, including

- `Injective`
- `Surjective`
- `IsOpenMap`
- `IsClosedMap`
- `GeneralizingMap`
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`
- `DenseRange` (`IsDominant`)

-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u v

section Injective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

instance : MorphismProperty.RespectsIso (topologically Function.Injective) :=
  topologically_respectsIso _ (fun e ↦ e.injective) (fun _ _ hf hg ↦ hg.comp hf)

/--
@isnad1 id=iszarisk.0h0v.s3.35e2e671ba74 from=seed src=0 shape=b8c8af52 vocab=dc2a8449
-/
instance injective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically Function.Injective) := by
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e ↦ ?_
  obtain ⟨i, hxi⟩ : ∃ i, f x₁ ∈ U i := by simpa using congr(f x₁ ∈ $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ ∈ U i from e ▸ hxi⟩ (Subtype.ext e))).1)

end Injective

section Surjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is surjective if the underlying map is. -/
@[mk_iff]
class Surjective : Prop where
  surj : Function.Surjective f

/--
@isnad1 id=eq.0h0v.s4.d15b5d6e9d85 from=seed src=0 shape=b383088a vocab=e306203c
-/
lemma surjective_eq_topologically :
    @Surjective = topologically Function.Surjective := by ext; exact surjective_iff _

/--
@isnad1 id=surjecti.0h3v.s7.7cc75fe5a20c from=seed src=0 shape=82a81c7a vocab=c770d24d
-/
@[grind .]
lemma Scheme.Hom.surjective (f : X ⟶ Y) [Surjective f] : Function.Surjective f :=
  Surjective.surj

instance (priority := 100) [IsIso f] : Surjective f := ⟨f.homeomorph.surjective⟩

instance [Surjective f] [Surjective g] : Surjective (f ≫ g) := ⟨g.surjective.comp f.surjective⟩

/--
@isnad1 id=surjecti.0h5v.s5.caace6cf9cfb from=seed src=0 shape=fca88495 vocab=096df828
-/
lemma Surjective.of_comp [Surjective (f ≫ g)] : Surjective g where
  surj := Function.Surjective.of_comp (g := f) (f ≫ g).surjective

instance (priority := low) [Nonempty X] [Subsingleton Y] (f : X ⟶ Y) :
    Surjective f := ⟨Function.surjective_to_subsingleton _⟩

/--
@isnad1 id=iff.0h5v.s5.fd80e63a697d from=seed src=0 shape=b557ed51 vocab=096df828
-/
lemma Surjective.comp_iff [Surjective f] : Surjective (f ≫ g) ↔ Surjective g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

instance : MorphismProperty.IsMultiplicative @Surjective.{u} where
  id_mem _ := inferInstance
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

instance : MorphismProperty.RespectsIso @Surjective :=
  surjective_eq_topologically ▸ topologically_respectsIso _ (fun e ↦ e.surjective)
    (fun _ _ hf hg ↦ hg.comp hf)

instance (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.HasOfPrecompProperty @Surjective P where
  of_precomp f g _ _ := .of_comp f g

/--
@isnad1 id=iszarisk.0h0v.s1.d231e428ceef from=seed src=0 shape=49959d42 vocab=4a224277
-/
instance surjective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Surjective := by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by simpa using congr(x ∈ $H)
  obtain ⟨⟨y, _⟩, hy⟩ := hf i ⟨x, hxi⟩
  exact ⟨y, congr(($hy).1)⟩

/--
@isnad1 id=eq.0h3v.s7.6787628cedf4 from=seed src=0 shape=656cedd1 vocab=e21129e0
-/
@[simp]
lemma range_eq_univ [Surjective f] : Set.range f = Set.univ := by
  simpa [Set.range_eq_univ] using f.surjective

/--
@isnad1 id=eq.1h6v.s8.e0bf6008b868 from=seed src=0 shape=6b33abeb vocab=1fc9d1d3
-/
lemma range_eq_range_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) : Set.range f = Set.range g := by
  rw [← hge]
  simp [Set.range_comp]

/--
@isnad1 id=iff.1h7v.s9.cc4514fd7307 from=seed src=0 shape=11514b01 vocab=59f0c540
-/
lemma mem_range_iff_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) (s : S) : s ∈ Set.range f ↔ s ∈ Set.range g := by
  rw [range_eq_range_of_surjective f g e hge]

/--
@isnad1 id=surjecti.1h4v.s8.a48b06b041ac from=seed src=0 shape=888d8aae vocab=b438c3b9
-/
lemma Surjective.sigmaDesc_of_union_range_eq_univ {X : Scheme.{u}}
    {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    (H : ⋃ i, Set.range (f i) = Set.univ) : Surjective (Limits.Sigma.desc f) := by
  refine ⟨fun x ↦ ?_⟩
  simp_rw [Set.eq_univ_iff_forall, Set.mem_iUnion] at H
  obtain ⟨i, x, rfl⟩ := H x
  use Limits.Sigma.ι Y i x
  rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]

instance {X : Scheme.{u}} {P : MorphismProperty Scheme.{u}} (𝒰 : X.Cover (Scheme.precoverage P)) :
    Surjective (Limits.Sigma.desc fun i ↦ 𝒰.f i) :=
  Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

/-- The single object covering by one surjective morphism satisfying `P`. -/
@[simps! I₀ X f]
def Scheme.Hom.cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Cover.{v} (precoverage P) S :=
  .singleton f <| by
    rw [singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩

/--
@isnad1 id=eq.0h5v.s5.dae1c9a9df43 from=seed src=0 shape=b67c289c vocab=c8e50861
-/
@[simp]
lemma Scheme.Hom.presieve₀_cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : P f) [Surjective f] : (f.cover hf).presieve₀ = Presieve.singleton f := by
  simp [cover]

instance {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Unique (Scheme.Hom.cover f hf).I₀ :=
  inferInstanceAs <| Unique PUnit

end Surjective

section Injective

/--
@isnad1 id=isstable.0h0v.s4.6e7e911700e3 from=seed src=0 shape=44653de4 vocab=e883f2fb
-/
instance injective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (topologically (Function.Injective ·)) where
  comp_mem _ _ hf hg := hg.comp hf

end Injective

section IsOpenMap

instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)

/--
@isnad1 id=iszarisk.0h0v.s4.42a4a69a0da2 from=seed src=0 shape=b8c8af52 vocab=b47a2108
-/
instance isOpenMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ ↦ hU.isOpenMap_iff_restrictPreimage

instance : IsZariskiLocalAtSource (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.isOpenMap_iff_comp

end IsOpenMap

section IsClosedMap

instance : (topologically IsClosedMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedMap) (fun _ _ hf hg ↦ hg.comp hf)

/--
@isnad1 id=iszarisk.0h0v.s4.80403745d0dc from=seed src=0 shape=b8c8af52 vocab=a833a62b
-/
instance isClosedMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsClosedMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ ↦ hU.isClosedMap_iff_restrictPreimage

end IsClosedMap

section IsEmbedding

instance : (topologically IsEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

/--
@isnad1 id=iszarisk.0h0v.s4.9a440a2ba35a from=seed src=0 shape=b8c8af52 vocab=34a17d90
-/
instance isEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isEmbedding_iff_restrictPreimage

end IsEmbedding

section IsOpenEmbedding

instance : (topologically IsOpenEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

/--
@isnad1 id=iszarisk.0h0v.s4.74951d3e45d4 from=seed src=0 shape=b8c8af52 vocab=030e179c
-/
instance isOpenEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsOpenEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isOpenEmbedding_iff_restrictPreimage

end IsOpenEmbedding

section IsClosedEmbedding

instance : (topologically IsClosedEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedEmbedding) (fun _ _ hf hg ↦ hg.comp hf)

/--
@isnad1 id=iszarisk.0h0v.s4.daa50ee2823a from=seed src=0 shape=b8c8af52 vocab=c609eeda
-/
instance isClosedEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsClosedEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isClosedEmbedding_iff_restrictPreimage

end IsClosedEmbedding

section IsDominant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is dominant if the underlying map has dense range. -/
@[mk_iff]
class IsDominant : Prop where
  denseRange : DenseRange f

/--
@isnad1 id=eq.0h0v.s5.b5c11070c235 from=seed src=0 shape=5b4bc6f3 vocab=e30adcfb
-/
lemma dominant_eq_topologically :
    @IsDominant = topologically DenseRange := by ext; exact isDominant_iff _

/--
@isnad1 id=denseran.0h3v.s7.beb9012f89bb from=seed src=0 shape=fcd0f1fe vocab=6be0c954
-/
lemma Scheme.Hom.denseRange (f : X ⟶ Y) [IsDominant f] : DenseRange f :=
  IsDominant.denseRange

instance (priority := 100) [Surjective f] : IsDominant f := ⟨f.surjective.denseRange⟩

instance [IsDominant f] [IsDominant g] : IsDominant (f ≫ g) :=
  ⟨g.denseRange.comp f.denseRange g.continuous⟩

instance : MorphismProperty.IsMultiplicative @IsDominant where
  id_mem := fun _ ↦ inferInstance
  comp_mem := fun _ _ _ _ ↦ inferInstance

/--
@isnad1 id=isdomina.0h5v.s5.f19c9daf5a01 from=seed src=0 shape=fca88495 vocab=87314943
-/
lemma IsDominant.of_comp [H : IsDominant (f ≫ g)] : IsDominant g := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f g))

/--
@isnad1 id=iff.0h5v.s5.1262fef9cc41 from=seed src=0 shape=b557ed51 vocab=87314943
-/
lemma IsDominant.comp_iff [IsDominant f] : IsDominant (f ≫ g) ↔ IsDominant g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=respects.0h0v.s2.e8a998258fda from=seed src=0 shape=25b03439 vocab=7e1dc24b
-/
instance IsDominant.respectsIso : MorphismProperty.RespectsIso @IsDominant :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦ inferInstance

/--
@isnad1 id=iszarisk.0h0v.s1.be5ef898855f from=seed src=0 shape=49959d42 vocab=892d2250
-/
instance IsDominant.isZariskiLocalAtTarget : IsZariskiLocalAtTarget @IsDominant :=
  have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isZariskiLocalAtTarget' DenseRange
    fun _ _ _ hU _ ↦ hU.denseRange_iff_restrictPreimage

/--
@isnad1 id=surjecti.1h3v.s7.1cbb03e2d469 from=seed src=0 shape=6aaa75a0 vocab=8730f587
-/
lemma surjective_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f]
    (hf : IsClosed (Set.range f)) :
    Surjective f :=
  ⟨by rw [← Set.range_eq_univ, ← hf.closure_eq, f.denseRange.closure_range]⟩

/--
@isnad1 id=isdomina.0h5v.s5.976f0642569f from=seed src=0 shape=77972de3 vocab=5dcc0f8f
-/
lemma IsDominant.of_comp_of_isOpenImmersion
    (f : X ⟶ Y) (g : Y ⟶ Z) [H : IsDominant (f ≫ g)] [IsOpenImmersion g] :
    IsDominant f := by
  rw [isDominant_iff, DenseRange] at H ⊢
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.injective]

/--
@isnad1 id=isdomina.1h2v.s5.8fd0e33892bd from=seed src=0 shape=7e1d4155 vocab=445bdabe
-/
lemma Opens.isDominant_ι {U : X.Opens} (hU : Dense (X := X) U) : IsDominant U.ι :=
  ⟨by simpa [DenseRange] using hU⟩

/--
@isnad1 id=isdomina.2h3v.s6.0a9a79b792f0 from=seed src=0 shape=232a24c6 vocab=1c156058
-/
lemma Opens.isDominant_homOfLE {U V : X.Opens} (hU : Dense (X := X) U) (hU' : U ≤ V) :
    IsDominant (X.homOfLE hU') :=
  have : IsDominant (X.homOfLE hU' ≫ V.ι) := by simpa using Opens.isDominant_ι hU
  IsDominant.of_comp_of_isOpenImmersion (g := V.ι) _

end IsDominant

section SpecializingMap

open TopologicalSpace

/--
@isnad1 id=respects.0h0v.s2.3bae364c65ef from=seed src=0 shape=0072ad64 vocab=6512ca45
-/
instance specializingMap_respectsIso : (topologically @SpecializingMap).RespectsIso := by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

/--
@isnad1 id=iszarisk.0h0v.s1.e64d6a99a759 from=seed src=0 shape=87ceb31f vocab=f715f753
-/
instance specializingMap_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically @SpecializingMap) := by
  apply topologically_isZariskiLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes_iff_mem_closure] at hcl
    exact ⟨⟨a, by simp [hay, hy]⟩, by simpa [closure_subtype], by simpa⟩
  · introv hU _ hsp
    simp_rw [specializingMap_iff_closure_singleton_subset] at hsp ⊢
    intro x y hy
    have : ∃ i, y ∈ U i := Opens.mem_iSup.mp (hU ▸ Opens.mem_top _)
    obtain ⟨i, hi⟩ := this
    rw [← specializes_iff_mem_closure] at hy
    have hfx : f x ∈ U i := (U i).2.stableUnderGeneralization hy hi
    have hy : (⟨y, hi⟩ : U i) ∈ closure {⟨f x, hfx⟩} := by
      simp only [closure_subtype, Set.image_singleton]
      rwa [← specializes_iff_mem_closure]
    obtain ⟨a, ha, hay⟩ := hsp i ⟨x, hfx⟩ hy
    rw [closure_subtype] at ha
    simp only [Opens.carrier_eq_coe, Set.image_singleton] at ha
    apply_fun Subtype.val at hay
    simp only [Opens.carrier_eq_coe, Set.restrictPreimage_coe] at hay
    use a.val, ha, hay

end SpecializingMap

section GeneralizingMap

instance : (topologically GeneralizingMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenEmbedding.generalizingMap)
    (fun _ _ hf hg ↦ hf.comp hg)

instance : IsZariskiLocalAtSource (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.generalizingMap_iff_comp

instance : IsZariskiLocalAtTarget (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtTarget' (fun _ ↦ _) fun _ _ _ hU _ ↦
    hU.generalizingMap_iff_restrictPreimage

end GeneralizingMap

end AlgebraicGeometry
