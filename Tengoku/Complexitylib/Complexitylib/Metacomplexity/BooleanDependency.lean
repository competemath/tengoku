/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Encoding

/-!
# Finite Boolean dependency tables

A function depending on a finite coordinate set can be represented by its
canonical table on assignments to that set. This module exposes exact
reconstruction, the `2^|S|` table-entry count, finiteness of the function's
range, and the corresponding range-cardinality bound. It also splits total
assignments bijectively across a coordinate set and its complement and proves
that uniform restriction is exactly uniform. Ordered finite coordinate sets
also receive computable exact-length assignment and truth-table codecs.
-/

public section

namespace Complexity

namespace BooleanDependency

/-- Splitting and then merging a total assignment recovers it exactly.
@isnad1 id=eq.0h3v.s6.3449527bfd92 from=translated src=- shape=5d99967b vocab=49b039f2
-/
@[simp] theorem mergeAssignments_split {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate) (input : coordinate → Bool) :
    mergeAssignments coordinates
        (restrict coordinates input, restrict coordinatesᶜ input) = input :=
  (assignmentSplitEquiv coordinates).left_inv input

/-- Restricting a merged assignment to its selected coordinates recovers the
selected component.
@isnad1 id=eq.0h4v.s7.7a56ac4ff470 from=translated src=- shape=0eac7fb7 vocab=49b039f2
-/
@[simp] theorem restrict_mergeAssignments_left {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (selected : coordinates → Bool)
    (outside : (coordinatesᶜ : Finset coordinate) → Bool) :
    restrict coordinates (mergeAssignments coordinates (selected, outside)) =
      selected :=
  congrArg Prod.fst ((assignmentSplitEquiv coordinates).right_inv
    (selected, outside))

/-- Restricting a merged assignment to the complement recovers the complement
component.
@isnad1 id=eq.0h4v.s7.b5303bd05df3 from=translated src=- shape=063a9109 vocab=49b039f2
-/
@[simp] theorem restrict_mergeAssignments_right {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (selected : coordinates → Bool)
    (outside : (coordinatesᶜ : Finset coordinate) → Bool) :
    restrict coordinatesᶜ
        (mergeAssignments coordinates (selected, outside)) = outside :=
  congrArg Prod.snd ((assignmentSplitEquiv coordinates).right_inv
    (selected, outside))

/-- Restricting a uniformly random total Boolean assignment to any finite
coordinate subset produces the exact uniform distribution on subset
assignments.
@isnad1 id=eq.0h3v.s8.5b9e01c94616 from=translated src=- shape=8f8ac515 vocab=37372250
-/
theorem uniformProbability_restrict {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (event : (coordinates → Bool) → Prop) [DecidablePred event] :
    uniformProbability (Finset.univ.filter fun input : coordinate → Bool =>
        event (restrict coordinates input)) =
      uniformProbability (Finset.univ.filter event) :=
  uniformProbability_restrict_internal coordinates event

/-- Extending a restricted assignment recovers every selected coordinate.
@isnad1 id=eq.1h4v.s5.14175800cbf4 from=translated src=- shape=31105d75 vocab=e2f5e782
-/
@[simp] theorem extendByFalse_restrict_apply {coordinate : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (input : coordinate → Bool) (index : coordinate)
    (hindex : index ∈ coordinates) :
    extendByFalse coordinates (restrict coordinates input) index = input index :=
  extendByFalse_restrict_apply_internal coordinates input index hindex

/-- If a function depends only on the selected coordinates, its canonical
table reconstructs its value on every total input.
@isnad1 id=eq.1h5v.s5.457eb0c6d7bb from=translated src=- shape=8912f752 vocab=63e89a9d
-/
@[simp] theorem table_restrict {coordinate result : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate))
    (input : coordinate → Bool) :
    table coordinates function (restrict coordinates input) = function input :=
  table_restrict_internal coordinates function hdepends input

/-- A table on `|S|` Boolean coordinates has exactly `2^|S|` entries.
@isnad1 id=eq.0h2v.s5.43aaa00e77d4 from=translated src=- shape=ffca3f88 vocab=1a0e7056
-/
theorem card_assignments {coordinate : Type*} (coordinates : Finset coordinate) :
    Nat.card (coordinates → Bool) = 2 ^ coordinates.card :=
  card_assignments_internal coordinates

/-- A function depending on finitely many Boolean coordinates has finite range.
@isnad1 id=finite.1h4v.s5.5401690bd20f from=translated src=- shape=216cf702 vocab=064699e4
-/
theorem finite_range_of_dependsOn {coordinate result : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate)) :
    (Set.range function).Finite :=
  finite_range_of_dependsOn_internal coordinates function hdepends

/-- A function depending on `S` has at most `2^|S|` distinct values.
@isnad1 id=le.1h4v.s5.b057b9e41bbd from=translated src=- shape=99f96c70 vocab=1bc1e716
-/
theorem card_range_le_pow_card_of_dependsOn
    {coordinate result : Type*} [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate)) :
    Nat.card (Set.range function) ≤ 2 ^ coordinates.card :=
  card_range_le_pow_card_of_dependsOn_internal coordinates function hdepends

end BooleanDependency

end Complexity
