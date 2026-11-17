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

/--
@isnad1 id=iff.0h5v.s5.a3e8fa5a5082 from=translated src=- shape=e2f8d3d6 vocab=afba7718
-/
@[simp] theorem mem_finiteFiberLabelPiece_iff
    {label : X → Fin n} {i : Fin n} {x : X} :
    x ∈ finiteFiberLabelPiece label i ↔ label x = i := by
  rfl

/--
@isnad1 id=measurab.1h4v.s5.ef0136ea8396 from=translated src=- shape=b0641e8d vocab=b87e4bdc
-/
theorem measurableSet_finiteFiberLabelPiece [MeasurableSpace X]
    {label : X → Fin n} (hlabel : Measurable label) (i : Fin n) :
    MeasurableSet (finiteFiberLabelPiece label i) :=
  (measurableSet_singleton i).preimage hlabel

/--
@isnad1 id=disjoint.1h5v.s6.4a6a259c5458 from=translated src=- shape=112b7737 vocab=0160d89f
-/
theorem disjoint_finiteFiberLabelPiece
    (label : X → Fin n) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (finiteFiberLabelPiece label i) (finiteFiberLabelPiece label j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact hij ((mem_finiteFiberLabelPiece_iff.mp hxi).symm.trans
    (mem_finiteFiberLabelPiece_iff.mp hxj))

/--
@isnad1 id=eq.0h3v.s4.729a21ed021e from=translated src=- shape=a1acae67 vocab=0c9ab946
-/
@[simp] theorem iUnion_finiteFiberLabelPiece (label : X → Fin n) :
    ⋃ i, finiteFiberLabelPiece label i = Set.univ := by
  ext x
  simp [finiteFiberLabelPiece]

/--
@isnad1 id=injon.1h6v.s5.7fc66b3cd0c6 from=translated src=- shape=ee817ff3 vocab=ce277406
-/
theorem IsMeasurableFiniteFiberLabeling.injOn_piece
    [MeasurableSpace X] {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label) (i : Fin n) :
    Set.InjOn f (finiteFiberLabelPiece label i) := by
  intro x hx x' hx' hfx
  exact hlabel.2 hfx ((mem_finiteFiberLabelPiece_iff.mp hx).trans
    (mem_finiteFiberLabelPiece_iff.mp hx').symm)

/--
@isnad1 id=isfinite.1h5v.s5.1db3b40a82a5 from=translated src=- shape=98c97d9a vocab=06ae9f6b
-/
theorem IsMeasurableFiniteFiberLabeling.isFiniteBorelInjectivePartition
    [MeasurableSpace X] {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label) :
    IsFiniteBorelInjectivePartition f (finiteFiberLabelPiece label) := by
  refine ⟨measurableSet_finiteFiberLabelPiece hlabel.1,
    ?_, iUnion_finiteFiberLabelPiece label, hlabel.injOn_piece⟩
  intro i j hij
  exact disjoint_finiteFiberLabelPiece label hij

/--
@isnad1 id=injon.1h6v.s5.79c95b2baaa0 from=translated src=- shape=ed55b091 vocab=35563f11
-/
theorem IsMeasurableFiniteFiberLabeling.injOn_fiber
    [MeasurableSpace X] {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label) (y : Y) :
    Set.InjOn label (f ⁻¹' ({y} : Set Y)) := by
  intro x hx x' hx' hlabelEq
  exact hlabel.2 (hx.trans hx'.symm) hlabelEq

/--
@isnad1 id=measurab.2h6v.s5.92c7759b966d from=translated src=- shape=f85c8154 vocab=ff068b01
-/
theorem IsMeasurableFiniteFiberLabeling.measurableSet_image_piece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label)
    (hf : Measurable f) (i : Fin n) :
    MeasurableSet (f '' finiteFiberLabelPiece label i) :=
  (measurableSet_finiteFiberLabelPiece hlabel.1 i).image_of_measurable_injOn
    hf (hlabel.injOn_piece i)

/--
@isnad1 id=ex.2h6v.s6.6dee97089813 from=translated src=- shape=73a0ab2a vocab=df0b1973
-/
theorem IsMeasurableFiniteFiberLabeling.exists_standardBorelCode_image_piece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {f : X → Y} {label : X → Fin n}
    (hlabel : IsMeasurableFiniteFiberLabeling f label)
    (hf : Measurable f) (i : Fin n) :
    ∃ c : StandardBorelCode Y, c.eval = f '' finiteFiberLabelPiece label i :=
  StandardBorelCode.exists_code (hlabel.measurableSet_image_piece hf i)

end DescriptiveSetTheory
