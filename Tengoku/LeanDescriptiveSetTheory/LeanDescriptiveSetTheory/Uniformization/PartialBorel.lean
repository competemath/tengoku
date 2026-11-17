/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.Relations
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Partial Borel functions

A partial function from `X` to `Y` is represented without a bundle: its domain is a set `s : Set X`
and its function has the native type `s → Y`.  Measurability therefore refers to the induced
measurable space on the subtype.  This module proves Borel graph and exact graph-code theorems,
singleton/empty section equations, and restriction/composition graph laws.

No converse from graph measurability to function measurability is asserted here.
-/

open MeasurableSpace Set

universe u v w

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A measurable partial map has a measurable native domain and a measurable subtype function.-/
def IsBorelPartialMap [MeasurableSpace X] [MeasurableSpace Y]
    (s : Set X) (f : s → Y) : Prop :=
  MeasurableSet s ∧ Measurable f

/-- Any measurable partial map between standard Borel spaces has a measurable graph.-/
theorem measurableSet_partialGraph [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {s : Set X} {f : s → Y}
    (hs : MeasurableSet s) (hf : Measurable f) : MeasurableSet (partialGraph s f) := by
  cases isEmpty_or_nonempty Y with
  | inl hY =>
      have hs0 : s = ∅ := by
        ext x
        constructor
        · intro hx
          exact isEmptyElim (f ⟨x, hx⟩)
        · simp
      subst s
      simp [partialGraph]
  | inr hY =>
      obtain ⟨g, hg, hgf⟩ :=
        (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend hf fun _ => hY
      have hgraph : partialGraph s f = s.graphOn g := by
        ext p
        constructor
        · rintro ⟨hp, hfp⟩
          apply Set.mem_graphOn.mpr
          refine ⟨hp, ?_⟩
          have h := congrFun hgf ⟨p.1, hp⟩
          exact h.trans hfp
        · intro h
          obtain ⟨hp, hgp⟩ := Set.mem_graphOn.mp h
          refine ⟨hp, ?_⟩
          have h := congrFun hgf ⟨p.1, hp⟩
          exact h.symm.trans hgp
      rw [hgraph]
      exact measurableSet_graphOn hs hg

theorem IsBorelPartialMap.measurableSet_partialGraph [MeasurableSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    {s : Set X} {f : s → Y} (h : IsBorelPartialMap s f) :
    MeasurableSet (partialGraph s f) :=
  DescriptiveSetTheory.measurableSet_partialGraph h.1 h.2

/-- A measurable partial map has an exact standard-Borel code for its graph.-/
theorem exists_standardBorelCode_partialGraph [MeasurableSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    {s : Set X} {f : s → Y} (hs : MeasurableSet s) (hf : Measurable f) :
    ∃ c : StandardBorelCode (X × Y), c.eval = partialGraph s f :=
  StandardBorelCode.exists_code (measurableSet_partialGraph hs hf)

/-- On its domain, a partial graph has exactly the selected singleton as vertical section.-/
theorem verticalSection_partialGraph_of_mem {s : Set X} (f : s → Y) {x : X}
    (hx : x ∈ s) : verticalSection (partialGraph s f) x = {f ⟨x, hx⟩} := by
  ext y
  constructor
  · rintro ⟨hx', hxy⟩
    rw [mem_singleton_iff]
    exact hxy.symm
  · intro hy
    have hy' : f ⟨x, hx⟩ = y := by
      rw [mem_singleton_iff] at hy
      exact hy.symm
    exact ⟨hx, hy'⟩

/-- Off its domain, a partial graph has an empty vertical section.-/
theorem verticalSection_partialGraph_of_not_mem {s : Set X} (f : s → Y) {x : X}
    (hx : x ∉ s) : verticalSection (partialGraph s f) x = ∅ := by
  ext y
  constructor
  · rintro ⟨hx', _⟩
    exact (hx hx').elim
  · simp

/-- Restrict a subtype-domain function to a smaller native subtype domain.-/
def partialMapRestrict {s u : Set X} (f : s → Y) (hu : u ⊆ s) : u → Y :=
  fun x => f ⟨x.1, hu x.2⟩

theorem measurable_partialMapRestrict [MeasurableSpace X] [MeasurableSpace Y]
    {s u : Set X} {f : s → Y} (hf : Measurable f) (hu : u ⊆ s) :
    Measurable (partialMapRestrict f hu) :=
  hf.comp (Measurable.subtype_mk measurable_subtype_coe)

/-- Restricting a partial map agrees exactly with first-coordinate restriction of its graph.-/
theorem partialGraph_partialMapRestrict {s u : Set X} (f : s → Y) (hu : u ⊆ s) :
    partialGraph u (partialMapRestrict f hu) = relationRestrict (partialGraph s f) u := by
  ext p
  constructor
  · rintro ⟨hp, hfp⟩
    exact ⟨⟨hu hp, hfp⟩, hp⟩
  · rintro ⟨⟨hp, hfp⟩, hpu⟩
    exact ⟨hpu, hfp⟩

/-- The native domain on which the value of `f` lies in the native domain of `g`.-/
def partialCompDomain (s : Set X) (f : s → Y) (t : Set Y) : Set X :=
  {x | ∃ hx : x ∈ s, f ⟨x, hx⟩ ∈ t}

/-- Compose two partial maps on the exact preimage domain.-/
noncomputable def partialMapComp {s : Set X} (f : s → Y) {t : Set Y} (g : t → Z) :
    partialCompDomain s f t → Z := fun x =>
  let hx : x.1 ∈ s := Classical.choose x.2
  let hfx : f ⟨x.1, hx⟩ ∈ t := Classical.choose_spec x.2
  g ⟨f ⟨x.1, hx⟩, hfx⟩

@[simp] theorem mem_partialCompDomain {s : Set X} {f : s → Y} {t : Set Y} {x : X} :
    x ∈ partialCompDomain s f t ↔ ∃ hx : x ∈ s, f ⟨x, hx⟩ ∈ t :=
  Iff.rfl

/-- The composite domain is the subtype-coercion image of the ordinary measurable preimage.-/
theorem partialCompDomain_eq_subtype_image {s : Set X} (f : s → Y) (t : Set Y) :
    partialCompDomain s f t = Subtype.val '' (f ⁻¹' t) := by
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

theorem measurableSet_partialCompDomain [MeasurableSpace X] [MeasurableSpace Y]
    {s : Set X} {f : s → Y} {t : Set Y} (hs : MeasurableSet s)
    (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (partialCompDomain s f t) := by
  rw [partialCompDomain_eq_subtype_image]
  exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 (hf ht)

theorem measurable_partialMapComp [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {s : Set X} {f : s → Y} {t : Set Y} {g : t → Z}
    (hf : Measurable f) (hg : Measurable g) : Measurable (partialMapComp f g) := by
  let lift : partialCompDomain s f t → s := fun x =>
    ⟨x.1, Classical.choose x.2⟩
  have hlift : Measurable lift := Measurable.subtype_mk measurable_subtype_coe
  let toSecondDomain : partialCompDomain s f t → t := fun x =>
    ⟨f (lift x), Classical.choose_spec x.2⟩
  have htoSecondDomain : Measurable toSecondDomain :=
    Measurable.subtype_mk (hf.comp hlift)
  exact hg.comp htoSecondDomain

/-- The graph of a partial composite is exactly relational composition of the two graphs.-/
theorem partialGraph_partialMapComp {s : Set X} (f : s → Y) {t : Set Y} (g : t → Z) :
    partialGraph (partialCompDomain s f t) (partialMapComp f g) =
      relationComp (partialGraph s f) (partialGraph t g) := by
  ext p
  constructor
  · rintro ⟨hp, hcomp⟩
    let hx : p.1 ∈ s := Classical.choose hp
    let hfx : f ⟨p.1, hx⟩ ∈ t := Classical.choose_spec hp
    refine ⟨f ⟨p.1, hx⟩, ⟨hx, rfl⟩, hfx, ?_⟩
    exact hcomp
  · rintro ⟨y, ⟨hx, hfy⟩, hy, hgz⟩
    have hp : p.1 ∈ partialCompDomain s f t := ⟨hx, hfy ▸ hy⟩
    refine ⟨hp, ?_⟩
    have hp' : ∃ hx' : p.1 ∈ s, f ⟨p.1, hx'⟩ ∈ t := hp
    let hx' : p.1 ∈ s := Classical.choose hp'
    let hfx' : f ⟨p.1, hx'⟩ ∈ t := Classical.choose_spec hp'
    change g ⟨f ⟨p.1, hx'⟩, hfx'⟩ = p.2
    have hsub : (⟨p.1, hx'⟩ : s) = ⟨p.1, hx⟩ := by
      exact Subtype.ext rfl
    have hin : (⟨f ⟨p.1, hx'⟩, hfx'⟩ : t) = ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa [hsub] using hfy
    exact (congrArg g hin).trans hgz

end DescriptiveSetTheory
