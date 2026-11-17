/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Relations.Basic
import Tengoku.Seed.MeasureTheory.MeasurableSpace.Constructions
import Tengoku.Seed.Topology.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sections of relations

Vertical and horizontal sections commute with the Boolean and countable operations used throughout
the library. The results here are pure set algebra unless their statements explicitly mention
topology or measurability.
-/

open Set

universe u v w

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- The vertical section of `R ⊆ X × Y` at `x`.-/
def verticalSection (R : Set (X × Y)) (x : X) : Set Y :=
  {y | (x, y) ∈ R}

/-- The horizontal section of `R ⊆ X × Y` at `y`.-/
def horizontalSection (R : Set (X × Y)) (y : Y) : Set X :=
  {x | (x, y) ∈ R}

@[simp] theorem mem_verticalSection {R : Set (X × Y)} {x : X} {y : Y} :
    y ∈ verticalSection R x ↔ (x, y) ∈ R :=
  Iff.rfl

@[simp] theorem mem_horizontalSection {R : Set (X × Y)} {x : X} {y : Y} :
    x ∈ horizontalSection R y ↔ (x, y) ∈ R :=
  Iff.rfl

@[simp] theorem verticalSection_swapRelation (R : Set (X × Y)) (y : Y) :
    verticalSection (swapRelation R) y = horizontalSection R y :=
  rfl

@[simp] theorem horizontalSection_swapRelation (R : Set (X × Y)) (x : X) :
    horizontalSection (swapRelation R) x = verticalSection R x :=
  rfl

@[simp] theorem verticalSection_compl (R : Set (X × Y)) (x : X) :
    verticalSection Rᶜ x = (verticalSection R x)ᶜ :=
  rfl

@[simp] theorem horizontalSection_compl (R : Set (X × Y)) (y : Y) :
    horizontalSection Rᶜ y = (horizontalSection R y)ᶜ :=
  rfl

@[simp] theorem verticalSection_empty (x : X) :
    verticalSection (∅ : Set (X × Y)) x = ∅ :=
  rfl

@[simp] theorem horizontalSection_empty (y : Y) :
    horizontalSection (∅ : Set (X × Y)) y = ∅ :=
  rfl

@[simp] theorem verticalSection_univ (x : X) :
    verticalSection (univ : Set (X × Y)) x = univ :=
  rfl

@[simp] theorem horizontalSection_univ (y : Y) :
    horizontalSection (univ : Set (X × Y)) y = univ :=
  rfl

@[simp] theorem verticalSection_union (R S : Set (X × Y)) (x : X) :
    verticalSection (R ∪ S) x = verticalSection R x ∪ verticalSection S x :=
  rfl

@[simp] theorem horizontalSection_union (R S : Set (X × Y)) (y : Y) :
    horizontalSection (R ∪ S) y = horizontalSection R y ∪ horizontalSection S y :=
  rfl

@[simp] theorem verticalSection_inter (R S : Set (X × Y)) (x : X) :
    verticalSection (R ∩ S) x = verticalSection R x ∩ verticalSection S x :=
  rfl

@[simp] theorem horizontalSection_inter (R S : Set (X × Y)) (y : Y) :
    horizontalSection (R ∩ S) y = horizontalSection R y ∩ horizontalSection S y :=
  rfl

@[simp] theorem verticalSection_iUnion {ι : Type w} (R : ι → Set (X × Y)) (x : X) :
    verticalSection (⋃ i, R i) x = ⋃ i, verticalSection (R i) x := by
  ext y
  simp

@[simp] theorem horizontalSection_iUnion {ι : Type w} (R : ι → Set (X × Y)) (y : Y) :
    horizontalSection (⋃ i, R i) y = ⋃ i, horizontalSection (R i) y := by
  ext x
  simp

@[simp] theorem verticalSection_iInter {ι : Type w} (R : ι → Set (X × Y)) (x : X) :
    verticalSection (⋂ i, R i) x = ⋂ i, verticalSection (R i) x := by
  ext y
  simp

@[simp] theorem horizontalSection_iInter {ι : Type w} (R : ι → Set (X × Y)) (y : Y) :
    horizontalSection (⋂ i, R i) y = ⋂ i, horizontalSection (R i) y := by
  ext x
  simp

@[simp] theorem verticalSection_relationPreimage {A : Type*} {B : Type*}
    (f : A → X) (g : B → Y) (R : Set (X × Y)) (a : A) :
    verticalSection (relationPreimage f g R) a = g ⁻¹' verticalSection R (f a) :=
  rfl

@[simp] theorem horizontalSection_relationPreimage {A : Type*} {B : Type*}
    (f : A → X) (g : B → Y) (R : Set (X × Y)) (b : B) :
    horizontalSection (relationPreimage f g R) b = f ⁻¹' horizontalSection R (g b) :=
  rfl

/-- Horizontal sections of an equivalence image are the corresponding parameter-coordinate
images.-/
theorem horizontalSection_relationEquivImage {X' : Type*} {Y' : Type*}
    (eX : X ≃ X') (eY : Y ≃ Y') (R : Set (X × Y)) (y' : Y') :
    horizontalSection (relationEquivImage eX eY R) y' =
      eX '' horizontalSection R (eY.symm y') := by
  rw [eX.image_eq_preimage_symm]
  rfl

/-- A vertical section of a composite relation is the union of the corresponding sections.-/
theorem verticalSection_relationComp {Z : Type w} (R : Set (X × Y)) (S : Set (Y × Z)) (x : X) :
    verticalSection (relationComp R S) x =
      ⋃ y ∈ verticalSection R x, verticalSection S y := by
  ext z
  simp

/-- A horizontal section of a composite relation is the union of the corresponding sections.-/
theorem horizontalSection_relationComp {Z : Type w} (R : Set (X × Y)) (S : Set (Y × Z))
    (z : Z) :
    horizontalSection (relationComp R S) z =
      ⋃ y ∈ horizontalSection S z, horizontalSection R y := by
  ext x
  simp [and_comm]

@[simp] theorem verticalSection_graphOn (s : Set X) (f : X → Y) (x : X) :
    verticalSection (s.graphOn f) x = {y | x ∈ s ∧ f x = y} := by
  ext y
  simp

@[simp] theorem horizontalSection_graphOn (s : Set X) (f : X → Y) (y : Y) :
    horizontalSection (s.graphOn f) y = {x | x ∈ s ∧ f x = y} := by
  ext x
  simp

/-- Every vertical section of an open relation is open.-/
theorem IsOpen.verticalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsOpen R) (x : X) : IsOpen (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- Every horizontal section of an open relation is open.-/
theorem IsOpen.horizontalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsOpen R) (y : Y) : IsOpen (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- Every vertical section of a closed relation is closed.-/
theorem IsClosed.verticalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) (x : X) : IsClosed (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- Every horizontal section of a closed relation is closed.-/
theorem IsClosed.horizontalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) (y : Y) : IsClosed (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- A vertical section of a measurable relation is measurable.-/
theorem MeasurableSet.verticalSection [MeasurableSpace X] [MeasurableSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (x : X) :
    MeasurableSet (verticalSection R x) :=
  (measurable_const.prodMk measurable_id) hR

/-- A horizontal section of a measurable relation is measurable.-/
theorem MeasurableSet.horizontalSection [MeasurableSpace X] [MeasurableSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    MeasurableSet (horizontalSection R y) :=
  (measurable_id.prodMk measurable_const) hR

end DescriptiveSetTheory
