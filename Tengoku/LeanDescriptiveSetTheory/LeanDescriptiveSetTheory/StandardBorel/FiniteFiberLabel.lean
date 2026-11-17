/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.Relations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite measurable labels for fibers

A measurable label `label : X → Fin n` separates the fibers of `f : X → Y` when two points with
the same `f`-value and the same label are equal.  Its label classes then form a finite Borel
partition of `X`, and `f` is injective on every part.  Lusin--Souslin makes the image of each part
Borel and therefore gives an exact standard-Borel code.

This is the explicitly retitled v1.47 fallback.  It verifies every consequence of a supplied
finite measurable fiber labeling, including genuinely finite fibers, but does not construct such a
labeling from the bare hypothesis that `f` is finite-to-one.  That existence statement still
depends on the unavailable general Lusin--Novikov machinery.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {n : ℕ}

/-- Every fiber of `f` is finite.-/
def HasFiniteFibers (f : X → Y) : Prop :=
  ∀ y, (f ⁻¹' ({y} : Set Y)).Finite

/-- A measurable finite label separates fibers of `f`.-/
def IsMeasurableFiniteFiberLabeling [MeasurableSpace X]
    (f : X → Y) (label : X → Fin n) : Prop :=
  Measurable label ∧
    ∀ ⦃x x'⦄, f x = f x' → label x = label x' → x = x'

/-- Existence of a measurable fiber-separating label into some finite type `Fin n`.-/
def HasMeasurableFiniteFiberLabeling [MeasurableSpace X] (f : X → Y) : Prop :=
  ∃ (n : ℕ) (label : X → Fin n), IsMeasurableFiniteFiberLabeling f label

/-- The Borel part carrying a fixed fiber label.-/
def finiteFiberLabelPiece (label : X → Fin n) (i : Fin n) : Set X :=
  label ⁻¹' {i}

/-- A finite Borel partition on whose parts `f` is injective.-/
def IsFiniteBorelInjectivePartition [MeasurableSpace X]
    (f : X → Y) (s : Fin n → Set X) : Prop :=
  (∀ i, MeasurableSet (s i)) ∧
    (∀ ⦃i j⦄, i ≠ j → Disjoint (s i) (s j)) ∧
    (⋃ i, s i) = Set.univ ∧
    ∀ i, Set.InjOn f (s i)

@[simp] theorem mem_finiteFiberLabelPiece_iff
    {label : X → Fin n} {i : Fin n} {x : X} :
    x ∈ finiteFiberLabelPiece label i ↔ label x = i := by
  rfl

theorem measurableSet_finiteFiberLabelPiece [MeasurableSpace X]
    {label : X → Fin n} (hlabel : Measurable label) (i : Fin n) :
    MeasurableSet (finiteFiberLabelPiece label i) :=
  (measurableSet_singleton i).preimage hlabel

theorem disjoint_finiteFiberLabelPiece
    (label : X → Fin n) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (finiteFiberLabelPiece label i) (finiteFiberLabelPiece label j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact hij ((mem_finiteFiberLabelPiece_iff.mp hxi).symm.trans
    (mem_finiteFiberLabelPiece_iff.mp hxj))

@[simp] theorem iUnion_finiteFiberLabelPiece (label : X → Fin n) :
    ⋃ i, finiteFiberLabelPiece label i = Set.univ := by
  ext x
  simp [finiteFiberLabelPiece]

theorem IsMeasurableFiniteFiberLabeling.injOn_piece
    [MeasurableSpace X] {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label) (i : Fin n) :
    Set.InjOn f (finiteFiberLabelPiece label i) := by
  intro x hx x' hx' hfx
  exact hlabel.2 hfx ((mem_finiteFiberLabelPiece_iff.mp hx).trans
    (mem_finiteFiberLabelPiece_iff.mp hx').symm)

theorem IsMeasurableFiniteFiberLabeling.isFiniteBorelInjectivePartition
    [MeasurableSpace X] {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label) :
    IsFiniteBorelInjectivePartition f (finiteFiberLabelPiece label) := by
  refine ⟨measurableSet_finiteFiberLabelPiece hlabel.1,
    ?_, iUnion_finiteFiberLabelPiece label, hlabel.injOn_piece⟩
  intro i j hij
  exact disjoint_finiteFiberLabelPiece label hij

theorem IsMeasurableFiniteFiberLabeling.injOn_fiber
    [MeasurableSpace X] {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label) (y : Y) :
    Set.InjOn label (f ⁻¹' ({y} : Set Y)) := by
  intro x hx x' hx' hlabelEq
  exact hlabel.2 (hx.trans hx'.symm) hlabelEq

theorem IsMeasurableFiniteFiberLabeling.measurableSet_image_piece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label)
    (hf : Measurable f) (i : Fin n) :
    MeasurableSet (f '' finiteFiberLabelPiece label i) :=
  (measurableSet_finiteFiberLabelPiece hlabel.1 i).image_of_measurable_injOn
    hf (hlabel.injOn_piece i)

theorem IsMeasurableFiniteFiberLabeling.exists_standardBorelCode_image_piece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label)
    (hf : Measurable f) (i : Fin n) :
    ∃ c : StandardBorelCode Y, c.eval = f '' finiteFiberLabelPiece label i :=
  StandardBorelCode.exists_code (hlabel.measurableSet_image_piece hf i)

end DescriptiveSetTheory
