/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Sites.MorphismProperty
public import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier

/-!
# Grothendieck topology defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated (pre)topology on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

## Implementation details

The pretopology is obtained from the precoverage `AlgebraicGeometry.Scheme.precoverage` defined in
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`. The definition is postponed to this file,
because the former does not have `HasPullbacks Scheme`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/--
The pretopology on the category of schemes defined by covering families where the components
satisfy `P`.
-/
def pretopology (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] : Pretopology Scheme.{u} :=
  (precoverage P).toPretopology

/-- The Grothendieck topology on the category of schemes induced by the pretopology defined by
`P`-covers. -/
abbrev grothendieckTopology (P : MorphismProperty Scheme.{u}) :
    GrothendieckTopology Scheme.{u} :=
  (precoverage P).toGrothendieck

instance : jointlySurjectivePrecoverage.IsStableUnderBaseChange :=
  isStableUnderBaseChange_comap_jointlySurjectivePrecoverage _
    fun f g _ ↦ pullbackComparison_forget_surjective f g

/-- The pretopology on the category of schemes defined by jointly surjective families. -/
def jointlySurjectivePretopology : Pretopology Scheme.{u} :=
  jointlySurjectivePrecoverage.toPretopology

variable {P : MorphismProperty Scheme.{u}}

/--
@isnad1 id=mem.0h3v.s6.322dcee01de8 from=seed src=0 shape=8267848b vocab=9041a9d4
-/
@[grind ←]
lemma Cover.mem_grothendieckTopology {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) :
    Sieve.ofArrows 𝒰.X 𝒰.f ∈ grothendieckTopology P X :=
  Precoverage.generate_mem_toGrothendieck 𝒰.mem₀

/--
@isnad1 id=mem.0h2v.s7.d5f7cb0fecf7 from=seed src=0 shape=1301c7d3 vocab=ffb4e1b9
-/
lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_precoverage _ X)

variable [P.IsStableUnderBaseChange] [P.IsMultiplicative]

/--
@isnad1 id=mem.0h3v.s6.50ba0b490fd7 from=seed src=0 shape=9654f3c9 vocab=a4cd6268
-/
@[grind ←]
lemma Cover.mem_pretopology {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)} :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ pretopology P X :=
  𝒰.mem₀

/--
@isnad1 id=iff.0h3v.s6.ea08f7885c8b from=seed src=0 shape=a6eab03f vocab=a4cd6268
-/
lemma mem_pretopology_iff {X : Scheme.{u}} {R : Presieve X} :
    R ∈ pretopology P X ↔ ∃ (𝒰 : Cover.{u + 1} (precoverage P) X),
    R = Presieve.ofArrows 𝒰.X 𝒰.f :=
  Precoverage.mem_iff_exists_zeroHypercover

/--
@isnad1 id=ex.1h3v.s6.1ab3f8b1eb09 from=seed src=0 shape=6d1e36bb vocab=a4cd6268
-/
alias ⟨exists_cover_of_mem_pretopology, _⟩ := mem_pretopology_iff

/--
@isnad1 id=iff.0h3v.s7.582e4617476e from=seed src=0 shape=08b392f5 vocab=5372d501
-/
lemma mem_grothendieckTopology_iff {X : Scheme.{u}} {S : Sieve X} :
    S ∈ grothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X), Presieve.ofArrows 𝒰.X 𝒰.f ≤ S := by
  simp_rw [grothendieckTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ ↦ ?_, fun ⟨𝒰, hle⟩ ↦ ⟨.ofArrows 𝒰.X 𝒰.f, 𝒰.mem_pretopology, hle⟩⟩
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨(𝒰 : Scheme.Cover _ _), rfl⟩ := hR
  use 𝒰.ulift, le_trans (fun Y g ⟨i⟩ ↦ .mk _) hle

/--
@isnad1 id=ex.1h3v.s7.568b0d372a1b from=seed src=0 shape=d29b117e vocab=5372d501
-/
alias ⟨exists_cover_of_mem_grothendieckTopology, _⟩ := mem_grothendieckTopology_iff

section

/-- The jointly surjective topology on `Scheme` is defined by the same condition as the jointly
surjective pretopology. -/
def jointlySurjectiveTopology : GrothendieckTopology Scheme.{u} :=
  jointlySurjectivePretopology.toGrothendieck.copy
    (fun X ↦ {s | ↑s ∈ jointlySurjectivePretopology X}) <|
    funext fun _ ↦ Set.ext fun s ↦
      ⟨fun ⟨_, hp, hps⟩ x ↦ let ⟨Y, u, hu, hmem⟩ := hp x;
        ⟨Y, u, Presieve.map_monotone hps _ _ hu, hmem⟩,
      fun hs ↦ ⟨s, hs, le_rfl⟩⟩

/--
@isnad1 id=iff.0h2v.s6.28ba1e83f1d8 from=seed src=0 shape=a86ab757 vocab=02f2f406
-/
theorem mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
    {X : Scheme.{u}} {s : Sieve X} :
    s ∈ jointlySurjectiveTopology X ↔ ↑s ∈ jointlySurjectivePretopology X :=
  Iff.rfl

/--
@isnad1 id=eq.0h0v.s3.582076e79a99 from=seed src=0 shape=0ab70a54 vocab=7f06bc4a
-/
lemma jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology :
    jointlySurjectiveTopology.{u} = jointlySurjectivePretopology.toGrothendieck :=
  GrothendieckTopology.copy_eq

variable (P)

/--
The pretopology defined by `P`-covers agrees with the
intersection of the pretopology of surjective families with the pretopology defined by `P`.
@isnad1 id=eq.0h1v.s5.f02206e57c7f from=seed src=0 shape=27f9b4ed vocab=95fcdc46
-/
lemma pretopology_eq_inf : pretopology P = jointlySurjectivePretopology ⊓ P.pretopology := rfl

/--
The Grothendieck topology defined by `P`-covers agrees with the Grothendieck
topology induced by the intersection of the pretopology of surjective families with
the pretopology defined by `P`.
@isnad1 id=eq.0h1v.s5.e948a3cbbf7f from=seed src=0 shape=4d14ddcf vocab=be67659c
-/
lemma grothendieckTopology_eq_inf :
    grothendieckTopology P = (jointlySurjectivePretopology ⊓ P.pretopology).toGrothendieck := by
  rw [grothendieckTopology, ← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  rfl

end

section

variable {P Q : MorphismProperty Scheme.{u}}

/--
@isnad1 id=le.1h2v.s6.69c483225914 from=seed src=0 shape=de01628d vocab=5cdd73db
-/
lemma grothendieckTopology_monotone (hPQ : P ≤ Q) :
    grothendieckTopology P ≤ grothendieckTopology Q :=
  Precoverage.toGrothendieck_mono (precoverage_mono hPQ)

variable [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/--
@isnad1 id=le.1h2v.s6.074e1cd5aa75 from=seed src=0 shape=c7b18801 vocab=248e144a
-/
lemma pretopology_monotone (hPQ : P ≤ Q) : pretopology P ≤ pretopology Q :=
  precoverage_mono hPQ

end

end AlgebraicGeometry.Scheme
