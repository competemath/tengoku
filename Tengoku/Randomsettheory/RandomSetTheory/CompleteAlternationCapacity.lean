/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CapacityFunctional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete alternation of hitting capacities

This file proves the finite-order form of a classical defining property of
random-set capacity functionals.  For a real-valued set functional `F`, we
use the union-difference convention

`Delta_A F(K) = F(K) - F(K ∪ A)`.

Thus a functional is completely alternating when every nonempty iterated
union difference is nonpositive.  With this sign convention, the avoidance
functional is dually completely monotone: all its iterated union differences
are nonnegative.

For a finite list `tests`, the proof identifies the two alternating
quantities exactly.  The common witness event is the event on which the
random set avoids the base test `K` but hits every member of `tests`:

* the iterated difference of avoidance probabilities is the probability of
  that witness event;
* for a nonempty list, the iterated difference of hitting probabilities is
  the negative of the same probability.

Lists are used rather than finite sets so that the reusable difference
operator records the order of iteration and also permits repeated tests.
The differences commute for the capacity and avoidance functionals by the
exact event formulas proved below.

No converse Choquet theorem is asserted here.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace RandomSetTheory

variable {Omega X : Type*} [MeasurableSpace Omega]

/-! ## Finite union differences and their witness event -/

/-- The union difference `Delta_A F(K) = F(K) - F(K ∪ A)`.

The sign is chosen so that increasing hitting functionals have nonpositive
first differences.-/
def unionDifference (A : Set X) (F : Set X -> Real) : Set X -> Real :=
  fun K => F K - F (K ∪ A)

/-- Iterated union differences along a finite list of tests.  The recursion
means

`iteratedUnionDifference (A :: tests) F K
    = iteratedUnionDifference tests F K
      - iteratedUnionDifference tests F (K ∪ A)`.

Equivalently this is `Delta_A` applied after the differences indexed by the
tail.-/
def iteratedUnionDifference : List (Set X) -> (Set X -> Real) -> Set X -> Real
  | [], F, K => F K
  | A :: tests, F, K =>
      iteratedUnionDifference tests F K -
        iteratedUnionDifference tests F (K ∪ A)

@[simp] theorem iteratedUnionDifference_nil (F : Set X -> Real) (K : Set X) :
    iteratedUnionDifference [] F K = F K :=
  rfl

@[simp] theorem iteratedUnionDifference_cons (A : Set X)
    (tests : List (Set X)) (F : Set X -> Real) (K : Set X) :
    iteratedUnionDifference (A :: tests) F K =
      iteratedUnionDifference tests F K -
        iteratedUnionDifference tests F (K ∪ A) :=
  rfl

/-- The event on which `S` hits every test in a finite list.-/
def hitEveryEvent (S : Omega -> Set X) : List (Set X) -> Set Omega
  | [] => Set.univ
  | A :: tests => hitEvent S A ∩ hitEveryEvent S tests

omit [MeasurableSpace Omega] in
@[simp] theorem hitEveryEvent_nil (S : Omega -> Set X) :
    hitEveryEvent S [] = Set.univ :=
  rfl

omit [MeasurableSpace Omega] in
@[simp] theorem hitEveryEvent_cons (S : Omega -> Set X) (A : Set X)
    (tests : List (Set X)) :
    hitEveryEvent S (A :: tests) = hitEvent S A ∩ hitEveryEvent S tests :=
  rfl

omit [MeasurableSpace Omega] in
@[simp] theorem mem_hitEveryEvent {S : Omega -> Set X}
    {tests : List (Set X)} {omega : Omega} :
    omega ∈ hitEveryEvent S tests <->
      ∀ A ∈ tests, omega ∈ hitEvent S A := by
  induction tests with
  | nil => simp
  | cons A tests ih => simp [hitEveryEvent, ih]

/-- The witness event for complete alternation: avoid the base test while
hitting every added test.-/
def alternationWitnessEvent (S : Omega -> Set X) (K : Set X)
    (tests : List (Set X)) : Set Omega :=
  avoidEvent S K ∩ hitEveryEvent S tests

omit [MeasurableSpace Omega] in
@[simp] theorem mem_alternationWitnessEvent {S : Omega -> Set X}
    {K : Set X} {tests : List (Set X)} {omega : Omega} :
    omega ∈ alternationWitnessEvent S K tests <->
      omega ∈ avoidEvent S K ∧
        ∀ A ∈ tests, omega ∈ hitEvent S A := by
  simp [alternationWitnessEvent]

omit [MeasurableSpace Omega] in
/-- Enlarging the base test can only shrink the alternation witness event.-/
theorem alternationWitnessEvent_union_subset (S : Omega -> Set X)
    (K A : Set X) (tests : List (Set X)) :
    alternationWitnessEvent S (K ∪ A) tests ⊆
      alternationWitnessEvent S K tests := by
  intro omega homega
  rcases homega with ⟨havoid, hall⟩
  exact ⟨(avoidEvent_antitone (Set.subset_union_left : K ⊆ K ∪ A)) havoid, hall⟩

omit [MeasurableSpace Omega] in
/-- Removing the witnesses that also avoid `A` is exactly the event that
additionally hits `A`.  This is the event-level engine behind all finite
orders of complete alternation.-/
theorem alternationWitnessEvent_sdiff_union (S : Omega -> Set X)
    (K A : Set X) (tests : List (Set X)) :
    alternationWitnessEvent S K tests \
        alternationWitnessEvent S (K ∪ A) tests =
      alternationWitnessEvent S K (A :: tests) := by
  ext omega
  simp only [alternationWitnessEvent, hitEveryEvent_cons,
    Set.mem_sdiff, Set.mem_inter_iff, mem_avoidEvent, mem_hitEvent]
  constructor
  · rintro ⟨⟨hKavoid, hTailHit⟩, hnot⟩
    refine ⟨hKavoid, ?_, hTailHit⟩
    by_contra hSA
    apply hnot
    refine ⟨?_, hTailHit⟩
    intro hhitUnion
    rcases hhitUnion with ⟨x, hxS, hxK | hxA⟩
    · exact hKavoid ⟨x, hxS, hxK⟩
    · exact hSA ⟨x, hxS, hxA⟩
  · rintro ⟨hKavoid, hAhit, hTailHit⟩
    refine ⟨⟨hKavoid, hTailHit⟩, ?_⟩
    rintro ⟨hKAavoid, _⟩
    exact hKAavoid (by
      rcases hAhit with ⟨x, hxS, hxA⟩
      exact ⟨x, hxS, Or.inr hxA⟩)

theorem measurableSet_hitEveryEvent {S : Omega -> Set X}
    {tests : List (Set X)}
    (h : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    MeasurableSet (hitEveryEvent S tests) := by
  induction tests with
  | nil => simp
  | cons A tests ih =>
      exact (h A (by simp)).inter (ih (fun B hB => h B (by simp [hB])))

theorem measurableSet_alternationWitnessEvent {S : Omega -> Set X}
    {K : Set X} {tests : List (Set X)}
    (hK : MeasurableSet (hitEvent S K))
    (h : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    MeasurableSet (alternationWitnessEvent S K tests) := by
  exact hK.compl.inter (measurableSet_hitEveryEvent h)

/-! ## Real-valued capacity and avoidance functionals -/

/-- The real-valued hitting functional.  Finiteness of the ambient measure
is imposed on the theorems that use subtraction, rather than on this
definition.-/
def capacityFunctionalReal (mu : Measure Omega) (S : Omega -> Set X)
    (K : Set X) : Real :=
  mu.real (hitEvent S K)

/-- The real-valued avoidance functional.-/
def avoidanceFunctionalReal (mu : Measure Omega) (S : Omega -> Set X)
    (K : Set X) : Real :=
  mu.real (avoidEvent S K)

@[simp] theorem capacityFunctionalReal_eq_toReal (mu : Measure Omega)
    (S : Omega -> Set X) (K : Set X) :
    capacityFunctionalReal mu S K = (capacityFunctional mu S K).toReal :=
  rfl

@[simp] theorem avoidanceFunctionalReal_eq_toReal (mu : Measure Omega)
    (S : Omega -> Set X) (K : Set X) :
    avoidanceFunctionalReal mu S K = (avoidanceFunctional mu S K).toReal :=
  rfl

/-! ## Exact complete monotonicity of avoidance -/

/-- Every finite iterated union difference of the avoidance functional is
exactly the measure of the alternation witness event.-/
theorem iteratedUnionDifference_avoidanceFunctionalReal_eq
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (tests : List (Set X))
    (hK : MeasurableSet (hitEvent S K))
    (hTests : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    iteratedUnionDifference tests (avoidanceFunctionalReal mu S) K =
      mu.real (alternationWitnessEvent S K tests) := by
  induction tests generalizing K with
  | nil =>
      simp [iteratedUnionDifference, avoidanceFunctionalReal,
        alternationWitnessEvent]
  | cons A tests ih =>
      have hA : MeasurableSet (hitEvent S A) := hTests A (by simp)
      have hTail : ∀ B ∈ tests, MeasurableSet (hitEvent S B) := by
        intro B hB
        exact hTests B (by simp [hB])
      have hKUnion : MeasurableSet (hitEvent S (K ∪ A)) := by
        rw [hitEvent_union]
        exact hK.union hA
      rw [iteratedUnionDifference_cons,
        ih K hK hTail, ih (K ∪ A) hKUnion hTail]
      let E : Set Omega := alternationWitnessEvent S K tests
      let F : Set Omega := alternationWitnessEvent S (K ∪ A) tests
      have hFE : F ⊆ E :=
        alternationWitnessEvent_union_subset S K A tests
      have hFmeas : MeasurableSet F :=
        measurableSet_alternationWitnessEvent hKUnion hTail
      rw [← measureReal_sdiff hFE hFmeas]
      exact congrArg mu.real (alternationWitnessEvent_sdiff_union S K A tests)

/-- Complete monotonicity of the real avoidance functional under finite
unions.-/
theorem avoidanceFunctionalReal_completeMonotonicity
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (tests : List (Set X))
    (hK : MeasurableSet (hitEvent S K))
    (hTests : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    0 ≤ iteratedUnionDifference tests (avoidanceFunctionalReal mu S) K := by
  rw [iteratedUnionDifference_avoidanceFunctionalReal_eq mu S K tests hK hTests]
  exact measureReal_nonneg

/-! ## Exact complete alternation of the hitting capacity -/

/-- For a measurable hitting event, the real hitting and avoidance
functionals add up to the mass of the whole space.-/
theorem capacityFunctionalReal_add_avoidanceFunctionalReal
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (hK : MeasurableSet (hitEvent S K)) :
    capacityFunctionalReal mu S K + avoidanceFunctionalReal mu S K =
      mu.real Set.univ := by
  simpa only [capacityFunctionalReal, avoidanceFunctionalReal,
    avoidEvent_eq_compl] using
      measureReal_add_measureReal_compl (μ := mu) hK

/-- Exact finite-order formula for the hitting capacity, including order
zero.  At order zero the constant `mu.real univ` remains; every nonempty
iteration cancels it and leaves the negative witness probability.-/
theorem iteratedUnionDifference_capacityFunctionalReal_eq
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (tests : List (Set X))
    (hK : MeasurableSet (hitEvent S K))
    (hTests : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    iteratedUnionDifference tests (capacityFunctionalReal mu S) K =
      (if tests = [] then mu.real Set.univ else 0) -
        mu.real (alternationWitnessEvent S K tests) := by
  induction tests generalizing K with
  | nil =>
      have hdual :=
        capacityFunctionalReal_add_avoidanceFunctionalReal mu S K hK
      simp only [iteratedUnionDifference_nil, ite_eq_left]
      simp only [alternationWitnessEvent, hitEveryEvent_nil,
        Set.inter_univ, avoidanceFunctionalReal] at hdual ⊢
      linarith
  | cons A tests ih =>
      have hA : MeasurableSet (hitEvent S A) := hTests A (by simp)
      have hTail : ∀ B ∈ tests, MeasurableSet (hitEvent S B) := by
        intro B hB
        exact hTests B (by simp [hB])
      have hKUnion : MeasurableSet (hitEvent S (K ∪ A)) := by
        rw [hitEvent_union]
        exact hK.union hA
      rw [iteratedUnionDifference_cons,
        ih K hK hTail, ih (K ∪ A) hKUnion hTail]
      let E : Set Omega := alternationWitnessEvent S K tests
      let F : Set Omega := alternationWitnessEvent S (K ∪ A) tests
      have hFE : F ⊆ E :=
        alternationWitnessEvent_union_subset S K A tests
      have hFmeas : MeasurableSet F :=
        measurableSet_alternationWitnessEvent hKUnion hTail
      have hmeasure :
          mu.real E - mu.real F =
            mu.real (alternationWitnessEvent S K (A :: tests)) := by
        rw [← measureReal_sdiff hFE hFmeas]
        exact congrArg mu.real (alternationWitnessEvent_sdiff_union S K A tests)
      simp only [List.cons_ne_nil, ite_false]
      linarith

/-- At every positive finite order, the iterated hitting-capacity difference
is the negative probability of avoiding the base while hitting all added
tests.  This is the numerical complete-alternation identity.-/
theorem iteratedUnionDifference_capacityFunctionalReal_eq_neg
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (tests : List (Set X)) (htests : tests ≠ [])
    (hK : MeasurableSet (hitEvent S K))
    (hTests : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    iteratedUnionDifference tests (capacityFunctionalReal mu S) K =
      -mu.real (alternationWitnessEvent S K tests) := by
  rw [iteratedUnionDifference_capacityFunctionalReal_eq
    mu S K tests hK hTests, ite_eq_right htests]
  ring

/-- Complete alternation of the real hitting capacity under finite unions.-/
theorem capacityFunctionalReal_completeAlternation
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (tests : List (Set X)) (htests : tests ≠ [])
    (hK : MeasurableSet (hitEvent S K))
    (hTests : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    iteratedUnionDifference tests (capacityFunctionalReal mu S) K ≤ 0 := by
  rw [iteratedUnionDifference_capacityFunctionalReal_eq_neg
    mu S K tests htests hK hTests]
  exact neg_nonpos.mpr measureReal_nonneg

/-- Numerical duality at every positive finite order: complete alternation of
the hitting functional is the negative of complete monotonicity of the
avoidance functional.-/
theorem iteratedUnionDifference_capacity_eq_neg_avoidance
    (mu : Measure Omega) [IsFiniteMeasure mu] (S : Omega -> Set X)
    (K : Set X) (tests : List (Set X)) (htests : tests ≠ [])
    (hK : MeasurableSet (hitEvent S K))
    (hTests : ∀ A ∈ tests, MeasurableSet (hitEvent S A)) :
    iteratedUnionDifference tests (capacityFunctionalReal mu S) K =
      -iteratedUnionDifference tests (avoidanceFunctionalReal mu S) K := by
  rw [iteratedUnionDifference_capacityFunctionalReal_eq_neg
      mu S K tests htests hK hTests,
    iteratedUnionDifference_avoidanceFunctionalReal_eq
      mu S K tests hK hTests]

/-! ## Classical compact-test specialization -/

section EffrosCompact

variable [MetricSpace X]

/-- The compact-test form used for random closed sets: Effros measurability
and closed values discharge every event-measurability hypothesis.-/
theorem capacityFunctionalReal_completeAlternation_compact_of_effros
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {S : Omega -> Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ omega, IsClosed (S omega))
    (K : Set X) (tests : List (Set X)) (htests : tests ≠ [])
    (hK : IsCompact K) (hTests : ∀ A ∈ tests, IsCompact A) :
    iteratedUnionDifference tests (capacityFunctionalReal mu S) K ≤ 0 := by
  apply capacityFunctionalReal_completeAlternation mu S K tests htests
  · exact measurableSet_hitEvent_compact hS hSclosed hK
  · intro A hA
    exact measurableSet_hitEvent_compact hS hSclosed (hTests A hA)

/-- Exact compact-test avoidance identity for an Effros random closed set.-/
theorem iteratedUnionDifference_avoidance_compact_of_effros_eq
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {S : Omega -> Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ omega, IsClosed (S omega))
    (K : Set X) (tests : List (Set X))
    (hK : IsCompact K) (hTests : ∀ A ∈ tests, IsCompact A) :
    iteratedUnionDifference tests (avoidanceFunctionalReal mu S) K =
      mu.real (alternationWitnessEvent S K tests) := by
  apply iteratedUnionDifference_avoidanceFunctionalReal_eq mu S K tests
  · exact measurableSet_hitEvent_compact hS hSclosed hK
  · intro A hA
    exact measurableSet_hitEvent_compact hS hSclosed (hTests A hA)

end EffrosCompact

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
