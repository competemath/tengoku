/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Counting

/-!
# Product counting inside conjunction majority events

A selected coordinate has at most two of the three allowed pair states. Selecting
both coordinates leaves at most one state, so their combined cost also satisfies
the product bound. Unused coordinates retain their two independent states.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Internal

open Entropy
open scoped BigOperators Classical

/-- The number of selected coordinates in one signed pair. -/
def pairSelected (mask : Bool → Bool) : ℕ :=
  (if mask false then 1 else 0) + (if mask true then 1 else 0)

/-- Local assignments satisfying a majority pair and any selected literals. -/
abbrev PairAllowed (a b : Bool) (mask bits : Bool → Bool) (x : Bool → Bool) : Prop :=
  ((x false == a) && (x true == b)) = false ∧ ∀ i, mask i = true → x i = bits i

/-- The three-state pair obeys the two-thirds cylinder bound. -/
theorem pair_count (a b : Bool) (mask bits : Bool → Bool) :
    3 ^ pairSelected mask * Fintype.card {x // PairAllowed a b mask bits x} ≤
      2 ^ pairSelected mask * 3 := by
  have hm : mask = fun i => if i then mask true else mask false := by
    ext i
    cases i <;> rfl
  have hb : bits = fun i => if i then bits true else bits false := by
    ext i
    cases i <;> rfl
  rw [hm, hb]
  generalize mask true = mt
  generalize mask false = mf
  generalize bits true = bt
  generalize bits false = bf
  cases a <;> cases b <;> cases mt <;> cases mf <;> cases bt <;> cases bf <;> decide

/-- A free Boolean coordinate also obeys the two-thirds cylinder bound. -/
theorem free_count (mask bit : Bool) :
    3 ^ (if mask then 1 else 0) *
        Fintype.card {x : Bool // mask = true → x = bit} ≤
      2 ^ (if mask then 1 else 0) * 2 := by
  cases mask <;> cases bit <;> decide

/-- Cardinalities factor when all constraints are local to one product coordinate. -/
theorem card_pi_constraints {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, Fintype (X i)] (P : ∀ i, X i → Prop) [∀ i, DecidablePred (P i)] :
    Fintype.card {x : ∀ i, X i // ∀ i, P i (x i)} =
      ∏ i, Fintype.card {x // P i x} := by
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := X) (p := P)), Fintype.card_pi]

/-- Split every original coordinate into a pair endpoint or an unused coordinate. -/
noncomputable def indexSplit {E V : Type*} (edge : E → SignedEdge V)
    (disjoint : Function.Injective (endpoint edge)) :
    (E × Bool) ⊕ {v : V // v ∉ Set.range (endpoint edge)} ≃ V :=
  (Equiv.sumCongr (Equiv.ofInjective (endpoint edge) disjoint) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun v => v ∈ Set.range (endpoint edge)))

/-- Selection counts add across all independent blocks. -/
theorem selected_count {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (mask : V → Bool) :
    (∑ e, pairSelected (fun b => mask (endpoint edge (e, b)))) +
      (∑ v : {v : V // v ∉ Set.range (endpoint edge)}, if mask v.val then 1 else 0) =
      ∑ v, if mask v then 1 else 0 := by
  have total := (indexSplit edge disjoint).sum_comp (fun v => if mask v then 1 else 0)
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at total
  change (∑ e : E, ∑ b : Bool, if mask (endpoint edge (e, b)) then 1 else 0) +
    (∑ v : {v : V // v ∉ Set.range (endpoint edge)}, if mask v.val then 1 else 0) =
    ∑ v, if mask v then 1 else 0 at total
  simpa only [Fintype.sum_bool, pairSelected, Nat.add_comm] using total

/-- Majority assignments with extra fixed literals factor into independent local counts. -/
theorem constrained_card {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (mask bits : V → Bool) :
    Fintype.card {x : V → Bool // (∀ e, (edge e).eval x = false) ∧
      ∀ v, mask v = true → x v = bits v} =
      (∏ e, Fintype.card {x // PairAllowed (edge e).leftSign (edge e).rightSign
        (fun b => mask (endpoint edge (e, b))) (fun b => bits (endpoint edge (e, b))) x}) *
      (∏ v : {v : V // v ∉ Set.range (endpoint edge)},
        Fintype.card {x : Bool // mask v.val = true → x = bits v.val}) := by
  let emb : E × Bool ↪ V := ⟨endpoint edge, disjoint⟩
  let R := {v : V // v ∉ Set.range (endpoint edge)}
  let split : (V → Bool) ≃ (E → Bool → Bool) × (R → Bool) :=
    (coordinateSplit emb).trans
      (Equiv.prodCongr (Equiv.curry E Bool Bool) (Equiv.refl _))
  let P (e : E) (x : Bool → Bool) := PairAllowed (edge e).leftSign (edge e).rightSign
    (fun b => mask (endpoint edge (e, b))) (fun b => bits (endpoint edge (e, b))) x
  let Q (v : R) (x : Bool) := mask v.val = true → x = bits v.val
  have equivalence (x : V → Bool) :
      ((∀ e, (edge e).eval x = false) ∧ ∀ v, mask v = true → x v = bits v) ↔
      ((∀ e, P e ((split x).1 e)) ∧ ∀ v, Q v ((split x).2 v)) := by
    constructor
    · rintro ⟨majority, fixed⟩
      constructor
      · intro e
        exact ⟨majority e, fun b => fixed (endpoint edge (e, b))⟩
      · intro v
        exact fixed v.val
    · rintro ⟨pairs, rest⟩
      constructor
      · intro e
        exact (pairs e).1
      · intro v hv
        by_cases used : v ∈ Set.range (endpoint edge)
        · obtain ⟨⟨e, b⟩, rfl⟩ := used
          exact (pairs e).2 b hv
        · exact rest ⟨v, used⟩ hv
  let reindex :
      {x : V → Bool // (∀ e, (edge e).eval x = false) ∧
        ∀ v, mask v = true → x v = bits v} ≃
      {y : (E → Bool → Bool) × (R → Bool) //
        (∀ e, P e (y.1 e)) ∧ ∀ v, Q v (y.2 v)} :=
    Equiv.subtypeEquiv split equivalence
  rw [Fintype.card_congr reindex,
    Fintype.card_congr (Equiv.subtypeProdEquivProd
      (p := fun y : E → Bool → Bool => ∀ e, P e (y e))
      (q := fun y : R → Bool => ∀ v, Q v (y v))),
    Fintype.card_prod]
  congr 1
  · exact card_pi_constraints P
  · convert card_pi_constraints Q using 1
    congr
    exact Subsingleton.elim _ _

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Internal
