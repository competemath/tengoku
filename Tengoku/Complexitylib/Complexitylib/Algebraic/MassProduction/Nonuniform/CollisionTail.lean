/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.Nonuniform.CollisionCut
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.Nonuniform.ConditionalCounting
public import Tengoku

/-!
# Exponential collision tails for independently chosen recovery sets

The proof applies to any finite family of recovery sets in which a fixed
point blocks at most one choice. A collision cut selects requests whose
failures become independent after the complementary directions are fixed.
Counting all such cuts proves an exponential bound without assuming that
the individual collision edges are independent.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped BigOperators

variable {Index Choice Point : Type*} [Fintype Index] [Fintype Choice]
  [DecidableEq Index] [DecidableEq Point]

/-- A request is clean if its recovery set avoids the occupied set and all
other requests' recovery sets. -/
def Clean (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (assignment : Index → Choice) (index : Index) : Prop :=
  Disjoint (sets index (assignment index)) occupied ∧
    ∀ other, other ≠ index →
      Disjoint (sets index (assignment index)) (sets other (assignment other))

/-- Nonclean request indices, including requests colliding with occupancy. -/
noncomputable def badRequests (sets : Index → Choice → Finset Point)
    (occupied : Finset Point) (assignment : Index → Choice) : Finset Index := by
  classical
  exact Finset.univ.filter fun index => ¬ Clean sets occupied assignment index

/-- The union of occupancy and the complementary requests, after their
directions have been fixed. -/
noncomputable def outsidePoints
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (selected : Finset Index) (outside : {index // index ∉ selected} → Choice) :
    Finset Point :=
  occupied ∪ Finset.univ.biUnion fun index => sets index.val (outside index)

omit [Fintype Choice] in
/-- Occupancy and the complementary recovery sets use at most the sum of
their individual point budgets. -/
theorem cardOutsidePoints_le
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (selected : Finset Index) (outside : {index // index ∉ selected} → Choice)
    (setSize : Nat) (setsSmall : ∀ index choice, (sets index choice).card ≤ setSize) :
    (outsidePoints sets occupied selected outside).card ≤
      occupied.card + Fintype.card Index * setSize := by
  classical
  calc
    _ ≤ occupied.card +
        (Finset.univ.biUnion fun index => sets index.val (outside index)).card :=
      Finset.card_union_le _ _
    _ ≤ occupied.card + ∑ index : {index // index ∉ selected},
        (sets index.val (outside index)).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ occupied.card + ∑ _index : {index // index ∉ selected}, setSize := by
      gcongr with index
      exact setsSmall _ _
    _ ≤ occupied.card + Fintype.card Index * setSize := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      gcongr
      exact Fintype.card_subtype_le _

end Algebraic.MassProduction.Nonuniform
