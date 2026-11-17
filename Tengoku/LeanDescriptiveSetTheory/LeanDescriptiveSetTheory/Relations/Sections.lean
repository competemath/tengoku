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

/--
@isnad1 id=iff.0h5v.s5.e6beb37f76b8 from=translated src=- shape=9b575362 vocab=66781aae
-/
@[simp] theorem mem_verticalSection {R : Set (X × Y)} {x : X} {y : Y} :
    y ∈ verticalSection R x ↔ (x, y) ∈ R :=
  Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.a3792e9d1bf8 from=translated src=- shape=4e583cad vocab=46d1e2bf
-/
@[simp] theorem mem_horizontalSection {R : Set (X × Y)} {x : X} {y : Y} :
    x ∈ horizontalSection R y ↔ (x, y) ∈ R :=
  Iff.rfl

/--
@isnad1 id=eq.0h4v.s4.8f396ec83778 from=translated src=- shape=2b97ffbb vocab=6125a52c
-/
@[simp] theorem verticalSection_swapRelation (R : Set (X × Y)) (y : Y) :
    verticalSection (swapRelation R) y = horizontalSection R y :=
  rfl

/--
@isnad1 id=eq.0h4v.s4.3d1e5b346653 from=translated src=- shape=a72380a6 vocab=6125a52c
-/
@[simp] theorem horizontalSection_swapRelation (R : Set (X × Y)) (x : X) :
    horizontalSection (swapRelation R) x = verticalSection R x :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.fdd03fba7bd5 from=translated src=- shape=e6d809b7 vocab=594fe1bf
-/
@[simp] theorem verticalSection_compl (R : Set (X × Y)) (x : X) :
    verticalSection Rᶜ x = (verticalSection R x)ᶜ :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.5849f6a0b987 from=translated src=- shape=7c835508 vocab=1fad2654
-/
@[simp] theorem horizontalSection_compl (R : Set (X × Y)) (y : Y) :
    horizontalSection Rᶜ y = (horizontalSection R y)ᶜ :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.f9d168c61026 from=translated src=- shape=e3eb21b4 vocab=93beae77
-/
@[simp] theorem verticalSection_empty (x : X) :
    verticalSection (∅ : Set (X × Y)) x = ∅ :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.829e9658d4a0 from=translated src=- shape=9db2ec0b vocab=fc408db2
-/
@[simp] theorem horizontalSection_empty (y : Y) :
    horizontalSection (∅ : Set (X × Y)) y = ∅ :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.ae8970b3fae9 from=translated src=- shape=e7fd64e9 vocab=118eb1d7
-/
@[simp] theorem verticalSection_univ (x : X) :
    verticalSection (univ : Set (X × Y)) x = univ :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.310caa7aca83 from=translated src=- shape=774c8edf vocab=7e5ef0d5
-/
@[simp] theorem horizontalSection_univ (y : Y) :
    horizontalSection (univ : Set (X × Y)) y = univ :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.c4be9201a788 from=translated src=- shape=40174ceb vocab=4e0ae942
-/
@[simp] theorem verticalSection_union (R S : Set (X × Y)) (x : X) :
    verticalSection (R ∪ S) x = verticalSection R x ∪ verticalSection S x :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.8289622a5067 from=translated src=- shape=40fdede0 vocab=b7a152d1
-/
@[simp] theorem horizontalSection_union (R S : Set (X × Y)) (y : Y) :
    horizontalSection (R ∪ S) y = horizontalSection R y ∪ horizontalSection S y :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.840689a883b6 from=translated src=- shape=40174ceb vocab=8e7edd37
-/
@[simp] theorem verticalSection_inter (R S : Set (X × Y)) (x : X) :
    verticalSection (R ∩ S) x = verticalSection R x ∩ verticalSection S x :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.f4fa12b63f09 from=translated src=- shape=40fdede0 vocab=c836d29b
-/
@[simp] theorem horizontalSection_inter (R S : Set (X × Y)) (y : Y) :
    horizontalSection (R ∩ S) y = horizontalSection R y ∩ horizontalSection S y :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.7ac4f9f2abd0 from=translated src=- shape=b59e6302 vocab=aa5c245d
-/
@[simp] theorem verticalSection_iUnion {ι : Type w} (R : ι → Set (X × Y)) (x : X) :
    verticalSection (⋃ i, R i) x = ⋃ i, verticalSection (R i) x := by
  ext y
  simp

/--
@isnad1 id=eq.0h5v.s5.f84e18922283 from=translated src=- shape=62c26c55 vocab=24e2131f
-/
@[simp] theorem horizontalSection_iUnion {ι : Type w} (R : ι → Set (X × Y)) (y : Y) :
    horizontalSection (⋃ i, R i) y = ⋃ i, horizontalSection (R i) y := by
  ext x
  simp

/--
@isnad1 id=eq.0h5v.s5.c488634a7986 from=translated src=- shape=b59e6302 vocab=bf2d7db6
-/
@[simp] theorem verticalSection_iInter {ι : Type w} (R : ι → Set (X × Y)) (x : X) :
    verticalSection (⋂ i, R i) x = ⋂ i, verticalSection (R i) x := by
  ext y
  simp

/--
@isnad1 id=eq.0h5v.s5.382e5ef81dec from=translated src=- shape=62c26c55 vocab=a7380c0c
-/
@[simp] theorem horizontalSection_iInter {ι : Type w} (R : ι → Set (X × Y)) (y : Y) :
    horizontalSection (⋂ i, R i) y = ⋂ i, horizontalSection (R i) y := by
  ext x
  simp

/--
@isnad1 id=eq.0h8v.s5.6d7d2def5c72 from=translated src=- shape=95f382ad vocab=2dbcf9a6
-/
@[simp] theorem verticalSection_relationPreimage {A : Type*} {B : Type*}
    (f : A → X) (g : B → Y) (R : Set (X × Y)) (a : A) :
    verticalSection (relationPreimage f g R) a = g ⁻¹' verticalSection R (f a) :=
  rfl

/--
@isnad1 id=eq.0h8v.s5.07ef7ed668ad from=translated src=- shape=21057550 vocab=47b66380
-/
@[simp] theorem horizontalSection_relationPreimage {A : Type*} {B : Type*}
    (f : A → X) (g : B → Y) (R : Set (X × Y)) (b : B) :
    horizontalSection (relationPreimage f g R) b = f ⁻¹' horizontalSection R (g b) :=
  rfl

/-- Horizontal sections of an equivalence image are the corresponding parameter-coordinate
images.
@isnad1 id=eq.0h8v.s6.ae44ebf398e4 from=translated src=- shape=3ee27fc9 vocab=dc8acf05
-/
theorem horizontalSection_relationEquivImage {X' : Type*} {Y' : Type*}
    (eX : X ≃ X') (eY : Y ≃ Y') (R : Set (X × Y)) (y' : Y') :
    horizontalSection (relationEquivImage eX eY R) y' =
      eX '' horizontalSection R (eY.symm y') := by
  rw [eX.image_eq_preimage_symm]
  rfl

/-- A vertical section of a composite relation is the union of the corresponding sections.
@isnad1 id=eq.0h6v.s6.4a7b3a1edd7d from=translated src=- shape=1b575961 vocab=ae2b1310
-/
theorem verticalSection_relationComp {Z : Type w} (R : Set (X × Y)) (S : Set (Y × Z)) (x : X) :
    verticalSection (relationComp R S) x =
      ⋃ y ∈ verticalSection R x, verticalSection S y := by
  ext z
  simp

/-- A horizontal section of a composite relation is the union of the corresponding sections.
@isnad1 id=eq.0h6v.s6.72964bb397e8 from=translated src=- shape=97407004 vocab=17d2a868
-/
theorem horizontalSection_relationComp {Z : Type w} (R : Set (X × Y)) (S : Set (Y × Z))
    (z : Z) :
    horizontalSection (relationComp R S) z =
      ⋃ y ∈ horizontalSection S z, horizontalSection R y := by
  ext x
  simp [and_comm]

/--
@isnad1 id=eq.0h5v.s5.7c4bf3ee684d from=translated src=- shape=63c336d4 vocab=d63cd4ca
-/
@[simp] theorem verticalSection_graphOn (s : Set X) (f : X → Y) (x : X) :
    verticalSection (s.graphOn f) x = {y | x ∈ s ∧ f x = y} := by
  ext y
  simp

/--
@isnad1 id=eq.0h5v.s5.6cae8123e4fa from=translated src=- shape=57152d69 vocab=65ad5469
-/
@[simp] theorem horizontalSection_graphOn (s : Set X) (f : X → Y) (y : Y) :
    horizontalSection (s.graphOn f) y = {x | x ∈ s ∧ f x = y} := by
  ext x
  simp

/-- Every vertical section of an open relation is open.
@isnad1 id=isopen.1h4v.s5.b247e9a9534c from=translated src=- shape=e7d49627 vocab=77c04757
-/
theorem IsOpen.verticalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsOpen R) (x : X) : IsOpen (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- Every horizontal section of an open relation is open.
@isnad1 id=isopen.1h4v.s5.3a80c5feea6e from=translated src=- shape=694ea159 vocab=d4dbe354
-/
theorem IsOpen.horizontalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsOpen R) (y : Y) : IsOpen (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- Every vertical section of a closed relation is closed.
@isnad1 id=isclosed.1h4v.s5.05c3a65b3bb7 from=translated src=- shape=e7d49627 vocab=b1a89f78
-/
theorem IsClosed.verticalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) (x : X) : IsClosed (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- Every horizontal section of a closed relation is closed.
@isnad1 id=isclosed.1h4v.s5.ffea847a9fce from=translated src=- shape=694ea159 vocab=2760ea1c
-/
theorem IsClosed.horizontalSection [TopologicalSpace X] [TopologicalSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) (y : Y) : IsClosed (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- A vertical section of a measurable relation is measurable.
@isnad1 id=measurab.1h4v.s5.c0215bb6a9fe from=translated src=- shape=e7d49627 vocab=bf7e3455
-/
theorem MeasurableSet.verticalSection [MeasurableSpace X] [MeasurableSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (x : X) :
    MeasurableSet (verticalSection R x) :=
  (measurable_const.prodMk measurable_id) hR

/-- A horizontal section of a measurable relation is measurable.
@isnad1 id=measurab.1h4v.s5.35d50fefd2ec from=translated src=- shape=694ea159 vocab=d02275f6
-/
theorem MeasurableSet.horizontalSection [MeasurableSpace X] [MeasurableSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    MeasurableSet (horizontalSection R y) :=
  (measurable_id.prodMk measurable_const) hR

end DescriptiveSetTheory
