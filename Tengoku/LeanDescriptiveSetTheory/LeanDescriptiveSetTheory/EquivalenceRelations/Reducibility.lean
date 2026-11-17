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

theorem IsBorelReduction.measurable [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) : Measurable f :=
  h.1

theorem IsBorelReduction.rel_iff [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) (x x' : X) : r x x' ↔ s (f x) (f x') :=
  h.2 x x'

theorem IsBorelReduction.preserves [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) {x x' : X} (hxx' : r x x') : s (f x) (f x') :=
  (h.rel_iff x x').1 hxx'

theorem IsBorelReduction.reflects [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} {f : X → Y}
    (h : IsBorelReduction r s f) {x x' : X} (hfx : s (f x) (f x')) : r x x' :=
  (h.rel_iff x x').2 hfx

theorem BorelReduces.exists_reduction [MeasurableSpace X] [MeasurableSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop} (h : BorelReduces r s) :
    ∃ f : X → Y, Measurable f ∧ ∀ x x', r x x' ↔ s (f x) (f x') :=
  h

/-- Borel reducibility is reflexive.-/
theorem BorelReduces.refl [MeasurableSpace X] (r : X → X → Prop) :
    BorelReduces r r :=
  ⟨id, measurable_id, fun _ _ ↦ Iff.rfl⟩

/-- Borel reductions compose in source-to-target order.-/
theorem BorelReduces.trans [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {r : X → X → Prop} {s : Y → Y → Prop} {t : Z → Z → Prop}
    (hrs : BorelReduces r s) (hst : BorelReduces s t) : BorelReduces r t := by
  rcases hrs with ⟨f, hf, hfs⟩
  rcases hst with ⟨g, hg, hgt⟩
  refine ⟨g ∘ f, hg.comp hf, fun x x' ↦ ?_⟩
  exact (hfs x x').trans (hgt (f x) (f x'))

/-- Every measurable pullback of a relation reduces to the original relation.-/
theorem borelReduces_pullback [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (r : Y → Y → Prop) :
    BorelReduces (pullbackEquivalenceRelation f r) r :=
  ⟨f, hf, fun _ _ ↦ Iff.rfl⟩

/-- Transport a relation to the codomain of a measurable equivalence.-/
def transportEquivalenceRelation [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) : Y → Y → Prop :=
  pullbackEquivalenceRelation e.symm r

theorem measurableEquiv_borelReduces_transport [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) :
    BorelReduces r (transportEquivalenceRelation e r) := by
  refine ⟨e, e.measurable, fun x x' ↦ ?_⟩
  simp [transportEquivalenceRelation, pullbackEquivalenceRelation]

theorem measurableEquiv_transport_borelReduces [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) :
    BorelReduces (transportEquivalenceRelation e r) r :=
  borelReduces_pullback e.symm e.symm.measurable r

/-- Borel reducibility is invariant when both relations are transported by measurable
equivalences.-/
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

theorem IsSmooth.standardBorelSpace [mX : MeasurableSpace X]
    {r : X → X → Prop} (h : IsSmooth r) : @StandardBorelSpace X mX :=
  h.1

/-- Smoothness is exactly Borel reducibility to equality on some standard Borel target.-/
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

/-- Smoothness descends along a Borel reduction.-/
theorem BorelReduces.isSmooth
    {X Y : Type u} [mX : MeasurableSpace X] [StandardBorelSpace X]
    [mY : MeasurableSpace Y] [StandardBorelSpace Y]
    {r : X → X → Prop} {s : Y → Y → Prop}
    (hrs : BorelReduces r s) (hs : IsSmooth s) : IsSmooth r := by
  rcases (isSmooth_iff_exists_borelReduces_eq (r := s)).1 hs with ⟨Z, mZ, hZ, hseq⟩
  exact (isSmooth_iff_exists_borelReduces_eq (r := r)).2
    ⟨Z, mZ, hZ, hrs.trans hseq⟩

/-- Smoothness is invariant under measurable equivalence of the underlying space.-/
theorem isSmooth_transport_iff
    {X Y : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (e : X ≃ᵐ Y) (r : X → X → Prop) :
    IsSmooth (transportEquivalenceRelation e r) ↔ IsSmooth r := by
  constructor
  · exact fun h ↦ (measurableEquiv_borelReduces_transport e r).isSmooth h
  · exact fun h ↦ (measurableEquiv_transport_borelReduces e r).isSmooth h

/-- Every smooth relation satisfies the equivalence-relation laws.-/
theorem IsSmooth.equivalence [MeasurableSpace X]
    {r : X → X → Prop} (h : IsSmooth r) : Equivalence r := by
  rcases h with ⟨_, Y, _, _, f, _, hrel⟩
  exact ⟨fun x ↦ (hrel x x).2 rfl,
    fun hxx' ↦ (hrel _ _).2 ((hrel _ _).1 hxx').symm,
    fun hxy hyz ↦ (hrel _ _).2 (((hrel _ _).1 hxy).trans ((hrel _ _).1 hyz))⟩

/-- Every smooth relation has a Borel graph.-/
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

/-- Equality on a standard Borel space is smooth.-/
theorem isSmooth_eq [mX : MeasurableSpace X] [StandardBorelSpace X] :
    IsSmooth (@Eq X) := by
  refine ⟨inferInstance, X, mX, inferInstance, id, measurable_id, ?_⟩
  exact fun _ _ ↦ Iff.rfl

/-- The universal relation is smooth, classified by a constant map to a universe lift of
`Unit`.-/
theorem isSmooth_universal [MeasurableSpace X] [StandardBorelSpace X] :
    IsSmooth (fun _ _ : X ↦ True) := by
  refine ⟨inferInstance, ULift.{u} Unit, inferInstance, inferInstance,
    fun _ ↦ ULift.up (), measurable_const, ?_⟩
  simp

/-- A relation explicitly induced by equality under a measurable map is smooth.-/
theorem isSmooth_pullback_eq [MeasurableSpace X] [StandardBorelSpace X]
    {Y : Type u} [MeasurableSpace Y] [StandardBorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    IsSmooth (pullbackEquivalenceRelation f (@Eq Y)) := by
  refine (isSmooth_iff_exists_borelReduces_eq (r := pullbackEquivalenceRelation f (@Eq Y))).2 ?_
  exact ⟨Y, inferInstance, inferInstance, borelReduces_pullback f hf (@Eq Y)⟩

/-- Every equivalence relation on a countable discrete measurable space is smooth, via its
setoid quotient equipped with the discrete measurable structure.-/
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

/-- Finite discrete equivalence relations are smooth.-/
theorem isSmooth_of_finite [MeasurableSpace X] [MeasurableSingletonClass X] [Finite X]
    {r : X → X → Prop} (hr : Equivalence r) : IsSmooth r :=
  isSmooth_of_countable hr

/-- The `E₀` prototype Borel reduces to itself.  This does not assert Borelness or smoothness.-/
theorem eventualEq_borelReduces_self : BorelReduces eventualEq eventualEq :=
  BorelReduces.refl eventualEq

end DescriptiveSetTheory
