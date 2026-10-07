/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Sites.Hypercover.ZeroFamily
public import Tengoku.Seed.AlgebraicGeometry.Sites.BigZariski
public import Tengoku.Seed.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compact precoverage

In this file we define the quasi-compact precoverage. A cover is covering in the quasi-compact
precoverage if it is a quasi-compact cover, i.e., if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

The fpqc precoverage is the precoverage by flat covers that are quasi-compact in this sense.
-/

@[expose] public section

universe w' w v u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/--
@isnad1 id=iff.0h2v.s4.3696228d291b from=seed src=0 shape=78f46704 vocab=6c8562bf
-/
@[simp]
lemma quasiCompactCover_shrink_iff (E : PreZeroHypercover.{w} S) :
    QuasiCompactCover E.shrink ↔ QuasiCompactCover E :=
  ⟨fun _ ↦ .of_hom E.fromShrink, fun _ ↦ .of_hom E.toShrink⟩

/-- The pre-`0`-hypercover family on the category of schemes underlying the fpqc precoverage. -/
@[simps]
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

/--
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
def qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

/--
@isnad1 id=iff.0h2v.s5.e72e73c4a9ea from=seed src=0 shape=0c7373db vocab=6c603e0b
-/
@[simp]
lemma presieve₀_mem_qcPrecoverage_iff {E : PreZeroHypercover.{w} S} :
    E.presieve₀ ∈ Scheme.qcPrecoverage S ↔ QuasiCompactCover E := by
  rw [← PreZeroHypercover.presieve₀_shrink, Scheme.qcPrecoverage,
    E.shrink.presieve₀_mem_precoverage_iff]
  simp

instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily fun X Y f hf ↦ by
  rw [qcCoverFamily_property, Scheme.quasiCompactCover_iff]
  infer_instance

instance : qcPrecoverage.IsStableUnderBaseChange := by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

instance : qcPrecoverage.IsStableUnderComposition := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

instance : qcPrecoverage.IsStableUnderSup := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

/--
@isnad1 id=mem.0h1v.s6.4537dece3b76 from=seed src=0 shape=4cf646e2 vocab=62e30474
-/
lemma bot_mem_qcPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ qcPrecoverage X := by
  rw [← PreZeroHypercover.presieve₀_empty.{0}, presieve₀_mem_qcPrecoverage_iff]
  infer_instance

/-- If `P` implies being an open map, the by `P` induced precoverage is coarser
than the quasi-compact precoverage.
@isnad1 id=le.1h1v.s8.93aa6874249a from=seed src=0 shape=900e4853 vocab=87c86411
-/
lemma precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P ≤ qcPrecoverage := by
  refine Precoverage.le_of_zeroHypercover fun X E ↦ ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i ↦ hP _ (Scheme.Cover.map_prop E i)

/--
@isnad1 id=le.0h0v.s4.fbf88503bbca from=seed src=0 shape=836e6cbb vocab=067d976f
-/
lemma zariskiPrecoverage_le_qcPrecoverage :
    zariskiPrecoverage ≤ qcPrecoverage :=
  precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenEmbedding.isOpenMap

/--
@isnad1 id=mem.0h3v.s5.528565916901 from=seed src=0 shape=98da1f33 vocab=9ba39884
-/
lemma Hom.singleton_mem_qcPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f ∈ qcPrecoverage Y := by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage, PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

section Property

variable {P : MorphismProperty Scheme.{u}}

/-- The `qc`-precoverage of a scheme wrt. to a morphism property `P` is the precoverage
given by quasi-compact covers satisfying `P`. -/
abbrev propQCPrecoverage (P : MorphismProperty Scheme.{u}) : Precoverage Scheme.{u} :=
  qcPrecoverage ⊓ Scheme.precoverage P

/--
@isnad1 id=le.0h1v.s4.1bd981793582 from=seed src=0 shape=1cbf026d vocab=931fcb70
-/
@[grind .]
lemma propQCPrecoverage_le_precoverage : propQCPrecoverage P ≤ precoverage P :=
  inf_le_right

/--
@isnad1 id=monotone.0h0v.s5.8e16c0c5b773 from=seed src=0 shape=6c822ea8 vocab=2d68f06f
-/
lemma propQCPrecoverage_monotone : Monotone propQCPrecoverage := by
  intro P Q h
  rw [propQCPrecoverage, propQCPrecoverage]
  gcongr
  exact precoverage_mono h

/--
@isnad1 id=le.0h1v.s5.b10015f21a66 from=seed src=0 shape=19e42a40 vocab=7621faad
-/
lemma zariskiPrecoverage_le_propQCPrecoverage [P.ContainsIdentities] [IsZariskiLocalAtSource P] :
    zariskiPrecoverage ≤ propQCPrecoverage P := by
  rw [propQCPrecoverage, le_inf_iff]
  refine ⟨zariskiPrecoverage_le_qcPrecoverage, precoverage_mono fun X Y f hf ↦ ?_⟩
  apply IsZariskiLocalAtSource.of_isOpenImmersion

instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.toPreZeroHypercover := by
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

/--
@isnad1 id=mem.0h2v.s6.dcd8793ae650 from=seed src=0 shape=9f899a30 vocab=393f1093
-/
lemma bot_mem_propQCPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ propQCPrecoverage P X :=
  ⟨bot_mem_qcPrecoverage _, bot_mem_precoverage _ _⟩

/-- Forget being quasi-compact. -/
@[simps toPreZeroHypercover]
abbrev Cover.forgetQc {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    S.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2

instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover := by
  dsimp; infer_instance

/-- Construct a cover in the `P`-qc topology from a quasi-compact cover in the `P`-topology. -/
@[simps toPreZeroHypercover]
def Cover.ofQuasiCompactCover {S : Scheme.{u}} (𝒰 : Scheme.Cover (precoverage P) S)
    [qc : QuasiCompactCover 𝒰.1] :
    Scheme.Cover (propQCPrecoverage P) S where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

/-- Lift a quasi-compact `P`-cover of a `u`-scheme in an arbitrary universe to universe `u`.
This is again quasi-compact. -/
noncomputable def Cover.qculift {S : Scheme.{u}} (𝒰 : Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] : Scheme.Cover.{u} (precoverage P) S where
  __ := 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨.inl x, 𝒰.covers _⟩, fun i ↦ ?_⟩
    induction i <;> exact 𝒰.map_prop _

instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [QuasiCompactCover 𝒰.1] :
    QuasiCompactCover (Scheme.Cover.qculift 𝒰).1 :=
  .of_hom (PreZeroHypercover.sumInr _ _)

instance : Precoverage.Small.{u} (propQCPrecoverage P) where
  zeroHypercoverSmall {S} (𝒰 : S.Cover _) := by
    refine ⟨𝒰.forgetQc.qculift.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i ↦ 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨Sum.inl x, 𝒰.forgetQc.covers _⟩, fun i ↦ 𝒰.forgetQc.map_prop _⟩

/--
@isnad1 id=iff.0h3v.s6.024d6f53b5ce from=seed src=0 shape=3856921b vocab=30dd9316
-/
lemma mem_propQCPrecoverage_iff_exists_quasiCompactCover {S : Scheme.{u}} {R : Presieve S} :
    R ∈ propQCPrecoverage P S ↔ ∃ (𝒰 : Scheme.Cover.{u + 1} (precoverage P) S),
      QuasiCompactCover 𝒰.toPreZeroHypercover ∧ R = 𝒰.presieve₀ := by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ ↦ ⟨𝒰.weaken propQCPrecoverage_le_precoverage, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ ↦ ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

/--
@isnad1 id=mem.0h5v.s5.07d6c0597b3c from=seed src=0 shape=b32a90ef vocab=07abc81e
-/
@[grind .]
lemma Hom.singleton_mem_propQCPrecoverage {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f ∈ propQCPrecoverage P Y := by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

/-- The `P`-`qc`-topology on the category of schemes wrt. to a morphism property `P` is the
topology generated by quasi-compact covers satisfying `P`. -/
abbrev propQCTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopology Scheme.{u} :=
  (propQCPrecoverage P).toGrothendieck

/--
@isnad1 id=mem.0h2v.s7.fa2e1207c7a6 from=seed src=0 shape=1301c7d3 vocab=7a7c0243
-/
lemma bot_mem_propQCTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ propQCTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_propQCPrecoverage X)

/--
@isnad1 id=mem.0h5v.s6.e9d92d3f5054 from=seed src=0 shape=06f9550d vocab=2fffa369
-/
@[grind .]
lemma Hom.generate_singleton_mem_propQCTopology {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
    [Surjective f] [QuasiCompact f] :
    .generate (.singleton f) ∈ propQCTopology P Y := by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propQCPrecoverage hf

/--
@isnad1 id=mem.0h3v.s6.73157d5b64e1 from=seed src=0 shape=cfef0c44 vocab=428a3d4f
-/
@[simp, grind .]
lemma Cover.mem_propQCTopology {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] :
    .ofArrows 𝒰.X 𝒰.f ∈ propQCTopology P S := by
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, 𝒰.mem₀⟩
  rwa [presieve₀_mem_qcPrecoverage_iff]

/--
@isnad1 id=le.0h1v.s4.4c7e25f32f07 from=seed src=0 shape=19e42a40 vocab=6e389783
-/
lemma zariskiTopology_le_propQCTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology ≤ propQCTopology P :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_propQCPrecoverage

end Property

end AlgebraicGeometry.Scheme
