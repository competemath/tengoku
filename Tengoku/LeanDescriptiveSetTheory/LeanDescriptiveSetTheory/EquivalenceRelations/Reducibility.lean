/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.EquivalenceRelations.CountableBorel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel reducibility and smoothness

`BorelReduces r s` means that one measurable map preserves and reflects the two relations; "Borel"
here refers to the supplied measurable structures.  The source relation is the first argument.
Smoothness is stated for a standard Borel source without fixing a coding space: it asks for a
measurable complete invariant in some standard Borel space in the same universe.

The API includes composition, transport by measurable equivalences, the equality-reduction
characterization of smoothness, and discrete countable examples.  No order notation, quotient
classification theorem, or nonsmoothness result is introduced here.
-/

open MeasurableSpace

universe u v w

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A specified map is a Borel reduction when it is measurable and preserves and reflects the
source relation.-/
def IsBorelReduction [MeasurableSpace X] [MeasurableSpace Y]
    (r : X → X → Prop) (s : Y → Y → Prop) (f : X → Y) : Prop :=
  Measurable f ∧ ∀ x x', r x x' ↔ s (f x) (f x')

/-- The source relation Borel reduces to the target relation.-/
def BorelReduces [MeasurableSpace X] [MeasurableSpace Y]
    (r : X → X → Prop) (s : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, IsBorelReduction r s f

/--
@isnad1 id=measurab.1h5v.s5.c0b810d9a394 from=translated src=- shape=291cf450 vocab=cc4dd605
-/
theorem IsBorelReduction.measurable [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) : Measurable f :=
  h.1

/--
@isnad1 id=iff.1h7v.s5.ac801437c057 from=translated src=- shape=7cb76a91 vocab=b41515b7
-/
theorem IsBorelReduction.rel_iff [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) (x x' : X) : r x x' ↔ s (f x) (f x') :=
  h.2 x x'

/--
@isnad1 id=var.1h8v.s5.63552608e4fb from=translated src=- shape=6f96fbf0 vocab=b41515b7
-/
theorem IsBorelReduction.preserves [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) {x x' : X} (hxx' : r x x') : s (f x) (f x') :=
  (h.rel_iff x x').1 hxx'

/--
@isnad1 id=var.1h8v.s5.032d251e35e8 from=translated src=- shape=16572344 vocab=b41515b7
-/
theorem IsBorelReduction.reflects [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) {x x' : X} (hfx : s (f x) (f x')) : r x x' :=
  (h.rel_iff x x').2 hfx

/--
@isnad1 id=ex.1h4v.s5.aab550249786 from=translated src=- shape=31d5b765 vocab=17b092a0
-/
theorem BorelReduces.exists_reduction [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} (h : BorelReduces r s) :
    ∃ f : X → Y, Measurable f ∧ ∀ x x', r x x' ↔ s (f x) (f x') :=
  h

/-- Borel reducibility is reflexive.
@isnad1 id=borelred.0h2v.s4.5425c13ad5ff from=translated src=- shape=71b2bee7 vocab=1c57f0de
-/
theorem BorelReduces.refl [MeasurableSpace X] (r : X → X → Prop) :
    BorelReduces r r :=
  ⟨id, measurable_id, fun _ _ ↦ Iff.rfl⟩

/-- Borel reductions compose in source-to-target order.
@isnad1 id=borelred.2h6v.s5.fef674c87277 from=translated src=- shape=f4daf3f8 vocab=1c57f0de
-/
theorem BorelReduces.trans [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {r : X → X → Prop} {s : Y → Y → Prop} {t : Z → Z → Prop}
    (hrs : BorelReduces r s) (hst : BorelReduces s t) : BorelReduces r t := by
  rcases hrs with ⟨f, hf, hfs⟩
  rcases hst with ⟨g, hg, hgt⟩
  refine ⟨g ∘ f, hg.comp hf, fun x x' ↦ ?_⟩
  exact (hfs x x').trans (hgt (f x) (f x'))

/-- Every measurable pullback of a relation reduces to the original relation.
@isnad1 id=borelred.1h4v.s5.b9a7e2fb2b75 from=translated src=- shape=aa27f409 vocab=1f8ab53b
-/
theorem borelReduces_pullback [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (r : Y → Y → Prop) :
    BorelReduces (pullbackEquivalenceRelation f r) r :=
  ⟨f, hf, fun _ _ ↦ Iff.rfl⟩

/-- Transport a relation to the codomain of a measurable equivalence.-/
def transportEquivalenceRelation [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) : Y → Y → Prop :=
  pullbackEquivalenceRelation e.symm r

/--
@isnad1 id=borelred.0h4v.s5.4789f8b18e92 from=translated src=- shape=e0183c88 vocab=53d3d005
-/
theorem measurableEquiv_borelReduces_transport [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) :
    BorelReduces r (transportEquivalenceRelation e r) := by
  refine ⟨e, e.measurable, fun x x' ↦ ?_⟩
  simp [transportEquivalenceRelation, pullbackEquivalenceRelation]

/--
@isnad1 id=borelred.0h4v.s5.6e8ac2b7019a from=translated src=- shape=fc77d174 vocab=53d3d005
-/
theorem measurableEquiv_transport_borelReduces [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) :
    BorelReduces (transportEquivalenceRelation e r) r :=
  borelReduces_pullback e.symm e.symm.measurable r

/-- Borel reducibility is invariant when both relations are transported by measurable
equivalences.
@isnad1 id=iff.0h8v.s6.d447249b5d40 from=translated src=- shape=09483546 vocab=53d3d005
-/
theorem borelReduces_transport_iff
    {X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace X'] [MeasurableSpace Y']
    (e : X ≃ᵐ X') (d : Y ≃ᵐ Y')
    (r : X → X → Prop) (s : Y → Y → Prop) :
    BorelReduces (transportEquivalenceRelation e r) (transportEquivalenceRelation d s) ↔
      BorelReduces r s := by
  constructor
  · intro h
    exact (measurableEquiv_borelReduces_transport e r).trans
      (h.trans (measurableEquiv_transport_borelReduces d s))
  · intro h
    exact (measurableEquiv_transport_borelReduces e r).trans
      (h.trans (measurableEquiv_borelReduces_transport d s))

/-- A measurable complete invariant takes equal values exactly on related inputs.-/
def HasMeasurableCompleteInvariant [MeasurableSpace X] [MeasurableSpace Y]
    (r : X → X → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x x', r x x' ↔ f x = f x'

/--
@isnad1 id=iff.0h3v.s4.81af13cc6943 from=translated src=- shape=7362a616 vocab=a18a914e
-/
theorem borelReduces_eq_iff [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} :
    BorelReduces r (@Eq Y) ↔ HasMeasurableCompleteInvariant (Y := Y) r :=
  Iff.rfl

/-- A relation is smooth when it has a measurable complete invariant in some standard Borel
space.  The target is universe-relative but is not fixed to a particular coding space.-/
def IsSmooth [mX : MeasurableSpace X] (r : X → X → Prop) : Prop :=
  @StandardBorelSpace X mX ∧
    ∃ (Y : Type u) (mY : MeasurableSpace Y),
      @StandardBorelSpace Y mY ∧
        @HasMeasurableCompleteInvariant X Y mX mY r

/--
@isnad1 id=standard.1h2v.s4.4ee18c27d8f8 from=translated src=- shape=b5fda10e vocab=a5e3374c
-/
theorem IsSmooth.standardBorelSpace [mX : MeasurableSpace X]
    {r : X → X → Prop} (h : IsSmooth r) : @StandardBorelSpace X mX :=
  h.1

/-- Smoothness is exactly Borel reducibility to equality on some standard Borel target.
@isnad1 id=iff.0h2v.s5.9c7bbc93c38c from=translated src=- shape=64924202 vocab=2e025a64
-/
theorem isSmooth_iff_exists_borelReduces_eq [mX : MeasurableSpace X]
    [StandardBorelSpace X]
    {r : X → X → Prop} :
    IsSmooth r ↔
      ∃ (Y : Type u) (mY : MeasurableSpace Y),
        @StandardBorelSpace Y mY ∧ @BorelReduces X Y mX mY r (@Eq Y) := by
  constructor
  · rintro ⟨_, Y, mY, hY, h⟩
    exact ⟨Y, mY, hY, (@borelReduces_eq_iff X Y mX mY r).2 h⟩
  · rintro ⟨Y, mY, hY, h⟩
    exact ⟨inferInstance, Y, mY, hY, (@borelReduces_eq_iff X Y mX mY r).1 h⟩

/-- Smoothness descends along a Borel reduction.
@isnad1 id=issmooth.2h4v.s5.bf02b91d068c from=translated src=- shape=04f73f19 vocab=2e025a64
-/
theorem BorelReduces.isSmooth
    {X Y : Type u} [mX : MeasurableSpace X] [StandardBorelSpace X]
    [mY : MeasurableSpace Y] [StandardBorelSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop}
    (hrs : BorelReduces r s) (hs : IsSmooth s) : IsSmooth r := by
  rcases (isSmooth_iff_exists_borelReduces_eq (r := s)).1 hs with ⟨Z, mZ, hZ, hseq⟩
  exact (isSmooth_iff_exists_borelReduces_eq (r := r)).2
    ⟨Z, mZ, hZ, hrs.trans hseq⟩

/-- Smoothness is invariant under measurable equivalence of the underlying space.
@isnad1 id=iff.0h4v.s5.3823124dccd1 from=translated src=- shape=3e323036 vocab=1241fb58
-/
theorem isSmooth_transport_iff
    {X Y : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) :
    IsSmooth (transportEquivalenceRelation e r) ↔ IsSmooth r := by
  constructor
  · exact fun h ↦ (measurableEquiv_borelReduces_transport e r).isSmooth h
  · exact fun h ↦ (measurableEquiv_transport_borelReduces e r).isSmooth h

/-- Every smooth relation satisfies the equivalence-relation laws.
@isnad1 id=equivale.1h2v.s4.95284d85cd11 from=translated src=- shape=fbf20e2a vocab=37614e56
-/
theorem IsSmooth.equivalence [MeasurableSpace X]
    {r : X → X → Prop} (h : IsSmooth r) : Equivalence r := by
  rcases h with ⟨_, Y, _, _, f, _, hrel⟩
  exact ⟨fun x ↦ (hrel x x).2 rfl,
    fun hxx' ↦ (hrel _ _).2 ((hrel _ _).1 hxx').symm,
    fun hxy hyz ↦ (hrel _ _).2 (((hrel _ _).1 hxy).trans ((hrel _ _).1 hyz))⟩

/-- Every smooth relation has a Borel graph.
@isnad1 id=isborelr.1h2v.s4.76c7eba51b7b from=translated src=- shape=fbf20e2a vocab=0817775e
-/
theorem IsSmooth.isBorelRelation [mX : MeasurableSpace X]
    {r : X → X → Prop} (h : IsSmooth r) : IsBorelRelation r := by
  rcases h with ⟨_, Y, mY, hY, f, hf, hrel⟩
  letI : MeasurableSpace Y := mY
  letI : StandardBorelSpace Y := hY
  have hr : r = pullbackEquivalenceRelation f (@Eq Y) := by
    funext x x'
    exact propext (hrel x x')
  rw [hr]
  exact (isCountableBorelEquivalenceRelation_eq (X := Y)).2.1.pullbackEquivalenceRelation hf

/-- Equality on a standard Borel space is smooth.
@isnad1 id=issmooth.0h1v.s3.226f18f6224a from=translated src=- shape=4c9b52a8 vocab=a5e3374c
-/
theorem isSmooth_eq [mX : MeasurableSpace X] [StandardBorelSpace X] :
    IsSmooth (@Eq X) := by
  refine ⟨inferInstance, X, mX, inferInstance, id, measurable_id, ?_⟩
  exact fun _ _ ↦ Iff.rfl

/-- The universal relation is smooth, classified by a constant map to a universe lift of
`Unit`.
@isnad1 id=issmooth.0h1v.s4.98995183f125 from=translated src=- shape=3f232fb4 vocab=a5e3374c
-/
theorem isSmooth_universal [MeasurableSpace X] [StandardBorelSpace X] :
    IsSmooth (fun _ _ : X ↦ True) := by
  refine ⟨inferInstance, ULift.{u} Unit, inferInstance, inferInstance,
    fun _ ↦ ULift.up (), measurable_const, ?_⟩
  simp

/-- A relation explicitly induced by equality under a measurable map is smooth.
@isnad1 id=issmooth.1h3v.s5.08366d39ec99 from=translated src=- shape=f5e0a9e5 vocab=456b6140
-/
theorem isSmooth_pullback_eq [MeasurableSpace X] [StandardBorelSpace X]
    {Y : Type u} [MeasurableSpace Y] [StandardBorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    IsSmooth (pullbackEquivalenceRelation f (@Eq Y)) := by
  refine (isSmooth_iff_exists_borelReduces_eq (r := pullbackEquivalenceRelation f (@Eq Y))).2 ?_
  exact ⟨Y, inferInstance, inferInstance, borelReduces_pullback f hf (@Eq Y)⟩

/-- Every equivalence relation on a countable discrete measurable space is smooth, via its
setoid quotient equipped with the discrete measurable structure.
@isnad1 id=issmooth.1h2v.s4.6ac996ec0cc9 from=translated src=- shape=b3981c83 vocab=62405105
-/
theorem isSmooth_of_countable [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    {r : X → X → Prop} (hr : Equivalence r) : IsSmooth r := by
  let s : Setoid X := ⟨r, hr⟩
  let mQ : MeasurableSpace (Quotient s) := ⊤
  refine ⟨inferInstance, Quotient s, mQ, ?_, ?_⟩
  · letI : MeasurableSpace (Quotient s) := mQ
    infer_instance
  · letI : MeasurableSpace (Quotient s) := mQ
    refine ⟨fun x ↦ Quotient.mk'' (s₁ := s) x, measurable_of_countable _, fun x x' ↦ ?_⟩
    constructor
    · intro h
      exact @Quotient.sound' X s x x' h
    · intro h
      exact (@Quotient.eq' X s x x').mp h

/-- Finite discrete equivalence relations are smooth.
@isnad1 id=issmooth.1h2v.s4.f49632e775cc from=translated src=- shape=b3981c83 vocab=fc17a2f0
-/
theorem isSmooth_of_finite [MeasurableSpace X] [MeasurableSingletonClass X] [Finite X]
    {r : X → X → Prop} (hr : Equivalence r) : IsSmooth r :=
  isSmooth_of_countable hr

/-- The `E₀` prototype Borel reduces to itself.  This does not assert Borelness or smoothness.
@isnad1 id=borelred.0h0v.s4.24b1b81a57ac from=translated src=- shape=5cc06927 vocab=9137cf7d
-/
theorem eventualEq_borelReduces_self : BorelReduces eventualEq eventualEq :=
  BorelReduces.refl eventualEq

end DescriptiveSetTheory
