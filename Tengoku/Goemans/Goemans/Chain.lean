/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.DeriveFintype
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.SplitIfs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Chain instances in the exit-cost model

This file formalizes Definition 6.1 and Lemmas 6.2--6.3 of the paper for an
arbitrary nonempty finite terminal type and an arbitrary finite chain.

The stage nodes are `v₀, ..., vₘ`. A stage arc `t : Fin m` is the arc from
`v_t` to `v_(t+1)`. Terminal `i` has an expensive exit at `e i` and a cheap
peel at `p i`, with `e i < p i`. Its expensive path traverses the stage arcs
with `t < e i`; its cheap path traverses those with `t < p i`. All stage and
cheap-exit costs are zero, and the private expensive exit of terminal `i` has
per-unit cost `c i`.

Unlike the prose shorthand that checks only chain arcs, `Admissible` below
quantifies over the complete arc type. Theorems `cheapExit_safe` and
`expensiveExit_safe` prove that private exits can never violate the
`x + dmax` allowance, and `admissible_iff_stage` then derives the shorthand.
-/

namespace Goemans
namespace Chain

universe u

/-- The arcs of an `m`-stage chain with private cheap and expensive exits.-/
inductive Arc (ι : Type u) (m : ℕ) : Type u
  | stage (t : Fin m)
  | cheapExit (i : ι)
  | expensiveExit (i : ι)
  deriving DecidableEq, Fintype

private def arcEquiv (ι : Type u) (m : ℕ) :
    Arc ι m ≃ (Fin m ⊕ (ι ⊕ ι)) where
  toFun
    | .stage t => .inl t
    | .cheapExit i => .inr (.inl i)
    | .expensiveExit i => .inr (.inr i)
  invFun
    | .inl t => .stage t
    | .inr (.inl i) => .cheapExit i
    | .inr (.inr i) => .expensiveExit i
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with t | i | i <;> rfl

/-- A finite-terminal chain instance in the exit-cost model.

`f i` units of terminal `i` use its cheap path in the fractional flow, while
`d i - f i` units use its expensive path.-/
structure Instance (ι : Type u) (m : ℕ) where
  /-- Positive terminal demands.-/
  d : ι → ℝ
  /-- Cheap-path amounts in the fractional flow.-/
  f : ι → ℝ
  /-- Expensive exit position.-/
  e : ι → Fin (m + 1)
  /-- Cheap peel position.-/
  p : ι → Fin (m + 1)
  /-- Per-unit costs on the private expensive exits.-/
  c : ι → ℝ
  d_pos : ∀ i, 0 < d i
  f_nonneg : ∀ i, 0 ≤ f i
  f_le_d : ∀ i, f i ≤ d i
  e_lt_p : ∀ i, e i < p i
  c_nonneg : ∀ i, 0 ≤ c i

namespace Instance

variable {ι : Type u} {m : ℕ}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (I : Instance ι m)

omit [DecidableEq ι] [Nonempty ι] in
private theorem sum_arc (g : Arc ι m → ℝ) :
    (∑ a, g a) =
      (∑ t, g (.stage t)) +
        ((∑ i, g (.cheapExit i)) + ∑ i, g (.expensiveExit i)) := by
  calc
    (∑ a, g a) =
        ∑ a : Fin m ⊕ (ι ⊕ ι), g ((arcEquiv ι m).symm a) :=
      Fintype.sum_equiv (arcEquiv ι m) g
        (fun a => g ((arcEquiv ι m).symm a)) (fun a => by simp)
    _ = (∑ t, g (.stage t)) +
          ((∑ i, g (.cheapExit i)) + ∑ i, g (.expensiveExit i)) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      rfl

/-- `dmax` is the largest terminal demand.-/
def dmax : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty I.d

omit [DecidableEq ι] in
/-- Every demand is at most `dmax`.
@isnad1 id=le.0h4v.s4.f9bc96a1d68f from=translated src=- shape=5b036231 vocab=765b35d5
-/
theorem d_le_dmax (i : ι) : I.d i ≤ I.dmax :=
  Finset.le_sup' I.d (Finset.mem_univ i)

omit [DecidableEq ι] in
/-- The maximum demand is positive.
@isnad1 id=lt.0h3v.s4.841391242829 from=translated src=- shape=0793b414 vocab=41cb8ae9
-/
theorem dmax_pos : 0 < I.dmax := by
  rcases ‹Nonempty ι› with ⟨i⟩
  exact lt_of_lt_of_le (I.d_pos i) (I.d_le_dmax i)

omit [Fintype ι] [DecidableEq ι] in
/-- With at least one terminal, the exit-before-peel invariant rules out a
zero-stage chain. This records the `m = 0` boundary explicitly rather than
letting later theorems appear to cover a realizable degenerate instance.
@isnad1 id=false.0h2v.s3.ab79e9e39839 from=translated src=- shape=4795f636 vocab=2cecc761
-/
theorem false_of_zero_stages (I : Instance ι 0) : False := by
  rcases ‹Nonempty ι› with ⟨i⟩
  have h := I.e_lt_p i
  omega

/-- Terminal `i` is in its cancellation interval `(e i, p i]` on stage arc
`t`, expressed with zero-based arc indices as `e i ≤ t < p i`.-/
def ActiveAt (i : ι) (t : Fin m) : Prop :=
  (I.e i).val ≤ t.val ∧ t.val < (I.p i).val

instance decidableActiveAt (i : ι) (t : Fin m) : Decidable (I.ActiveAt i t) :=
  by
    unfold ActiveAt
    infer_instance

/-- Fractional load on a stage arc.-/
def stageX (t : Fin m) : ℝ :=
  ∑ i, ((if t.val < (I.p i).val then I.f i else 0) +
    (if t.val < (I.e i).val then I.d i - I.f i else 0))

/-- Unsplittable load on a stage arc. `S` is the set routed cheaply.-/
def stageLoad (S : Finset ι) (t : Fin m) : ℝ :=
  ∑ i, if i ∈ S then
    (if t.val < (I.p i).val then I.d i else 0)
  else
    (if t.val < (I.e i).val then I.d i else 0)

/-- Fractional load on a complete chain arc.-/
def x : Arc ι m → ℝ
  | .stage t => I.stageX t
  | .cheapExit i => I.f i
  | .expensiveExit i => I.d i - I.f i

/-- Unsplittable load on a complete chain arc.-/
def load (S : Finset ι) : Arc ι m → ℝ
  | .stage t => I.stageLoad S t
  | .cheapExit i => if i ∈ S then I.d i else 0
  | .expensiveExit i => if i ∈ S then 0 else I.d i

/-- Per-unit arc costs in the exit-cost model.-/
def arcCost : Arc ι m → ℝ
  | .stage _ => 0
  | .cheapExit _ => 0
  | .expensiveExit i => I.c i

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every arc cost is nonnegative.
@isnad1 id=le.0h4v.s4.4f29c54d4483 from=translated src=- shape=4563df6a vocab=8f77fb79
-/
theorem arcCost_nonneg (a : Arc ι m) : 0 ≤ I.arcCost a := by
  cases a with
  | stage _ => simp [arcCost]
  | cheapExit _ => simp [arcCost]
  | expensiveExit i => simpa [arcCost] using I.c_nonneg i

/-- Fractional cost; only private expensive exits carry cost.-/
def fractionalCost : ℝ :=
  ∑ i, I.c i * (I.d i - I.f i)

/-- Cost of routing exactly the terminals in `S` cheaply.-/
def routingCost (S : Finset ι) : ℝ :=
  ∑ i, if i ∈ S then 0 else I.c i * I.d i

omit [DecidableEq ι] [Nonempty ι] in
/-- The exit-cost shorthand `fractionalCost` is exactly the ordinary cost
sum over every arc of the complete chain graph. Stage and cheap-exit terms
vanish because their per-unit costs are zero.
@isnad1 id=eq.0h3v.s5.e352f1a77004 from=translated src=- shape=af92aff4 vocab=ab32f9f4
-/
theorem fractionalCost_eq_sum_arc :
    I.fractionalCost = ∑ a : Arc ι m, I.arcCost a * I.x a := by
  rw [sum_arc]
  simp [fractionalCost, arcCost, x]

omit [Nonempty ι] in
/-- The exit-cost shorthand `routingCost S` is exactly the ordinary cost
sum over every arc of the complete unsplittable routing load.
@isnad1 id=eq.0h4v.s6.e09990a14c5b from=translated src=- shape=c0d1780d vocab=e42ae619
-/
theorem routingCost_eq_sum_arc (S : Finset ι) :
    I.routingCost S = ∑ a : Arc ι m, I.arcCost a * I.load S a := by
  rw [sum_arc]
  simp [routingCost, arcCost, load]

/-- Full-graph admissibility under the Dinitz--Garg--Goemans allowance.-/
def Admissible (S : Finset ι) : Prop :=
  ∀ a, I.load S a ≤ I.x a + I.dmax

/-- The contribution of terminal `i` to `load - x` on stage `t`.

Outside `(e i, p i]` it cancels. Inside that interval it is `d i - f i` when
`i` is routed cheaply and `-f i` when routed expensively.-/
def excessTerm (S : Finset ι) (t : Fin m) (i : ι) : ℝ :=
  if I.ActiveAt i t then
    if i ∈ S then I.d i - I.f i else -I.f i
  else 0

/-- Total load excess on a stage arc after cancellation.-/
def stageExcess (S : Finset ι) (t : Fin m) : ℝ :=
  ∑ i, I.excessTerm S t i

omit [Fintype ι] [Nonempty ι] in
private theorem terminal_stage_diff (S : Finset ι) (t : Fin m) (i : ι) :
    (if i ∈ S then
        (if t.val < (I.p i).val then I.d i else 0)
      else
        (if t.val < (I.e i).val then I.d i else 0)) -
      ((if t.val < (I.p i).val then I.f i else 0) +
        (if t.val < (I.e i).val then I.d i - I.f i else 0)) =
      I.excessTerm S t i := by
  have hep := I.e_lt_p i
  by_cases hi : i ∈ S <;>
    by_cases hte : t.val < (I.e i).val <;>
      by_cases htp : t.val < (I.p i).val
  all_goals simp [excessTerm, ActiveAt, hi, hte, htp]
  all_goals try omega

omit [Nonempty ι] in
/-- **Lemma 6.2, cancellation identity.** On every stage arc, routing load
minus fractional load is the sum of the active terminals' signed
contributions. Terminals at or before their expensive exit are load-neutral.
@isnad1 id=eq.0h5v.s5.3957c6f2b9ae from=translated src=- shape=cf89d0d7 vocab=36056f08
-/
theorem stageLoad_sub_stageX (S : Finset ι) (t : Fin m) :
    I.stageLoad S t - I.stageX t = I.stageExcess S t := by
  rw [stageLoad, stageX, stageExcess, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => I.terminal_stage_diff S t i

omit [Nonempty ι] in
/-- The same cancellation identity through the complete-arc API.
@isnad1 id=eq.0h5v.s5.1094051e6aa5 from=translated src=- shape=8aab788b vocab=636d0ae9
-/
theorem load_sub_x_stage (S : Finset ι) (t : Fin m) :
    I.load S (.stage t) - I.x (.stage t) = I.stageExcess S t :=
  I.stageLoad_sub_stageX S t

/-- A private cheap exit can never violate `x + dmax`.
@isnad1 id=le.0h5v.s5.d6f52225cb64 from=translated src=- shape=92ba30f8 vocab=01530dd4
-/
theorem cheapExit_safe (S : Finset ι) (i : ι) :
    I.load S (.cheapExit i) ≤ I.x (.cheapExit i) + I.dmax := by
  rw [load, x]
  split_ifs
  · linarith [I.f_nonneg i, I.d_le_dmax i]
  · linarith [I.f_nonneg i, I.dmax_pos]

/-- A private expensive exit can never violate `x + dmax`.
@isnad1 id=le.0h5v.s5.3d2392bb9f35 from=translated src=- shape=92ba30f8 vocab=7b6943fb
-/
theorem expensiveExit_safe (S : Finset ι) (i : ι) :
    I.load S (.expensiveExit i) ≤ I.x (.expensiveExit i) + I.dmax := by
  rw [load, x]
  split_ifs
  · linarith [I.f_le_d i, I.dmax_pos]
  · linarith [I.f_le_d i, I.d_le_dmax i]

/-- Full admissibility is equivalent to checking only stage arcs.
@isnad1 id=iff.0h4v.s5.212453e44dae from=translated src=- shape=b0ff46b0 vocab=d7a2ca4f
-/
theorem admissible_iff_stage (S : Finset ι) :
    I.Admissible S ↔ ∀ t, I.stageLoad S t ≤ I.stageX t + I.dmax := by
  constructor
  · intro h t
    exact h (.stage t)
  · intro h a
    cases a with
    | stage t => exact h t
    | cheapExit i => exact I.cheapExit_safe S i
    | expensiveExit i => exact I.expensiveExit_safe S i

omit [Fintype ι] [Nonempty ι] in
private theorem excessTerm_mono {S T : Finset ι} (hST : S ⊆ T)
    (t : Fin m) (i : ι) :
    I.excessTerm S t i ≤ I.excessTerm T t i := by
  by_cases ha : I.ActiveAt i t
  · by_cases hiS : i ∈ S
    · have hiT := hST hiS
      simp [excessTerm, ha, hiS, hiT]
    · by_cases hiT : i ∈ T
      · simp only [excessTerm, ha, hiS, hiT, ite_true, ite_false]
        linarith [I.d_pos i]
      · simp [excessTerm, ha, hiS, hiT]
  · simp [excessTerm, ha]

omit [Nonempty ι] in
/-- Stage excess is monotone in the set of cheaply routed terminals.
@isnad1 id=le.1h6v.s5.ecb332ee20b0 from=translated src=- shape=574b90e9 vocab=5caedaf8
-/
theorem stageExcess_mono {S T : Finset ι} (hST : S ⊆ T) (t : Fin m) :
    I.stageExcess S t ≤ I.stageExcess T t := by
  apply Finset.sum_le_sum
  intro i _
  exact I.excessTerm_mono hST t i

omit [Nonempty ι] in
/-- Removing a terminal that is inactive at a stage does not change the
stage excess. This makes precise that routing choices matter only on the
terminal's cancellation interval.
@isnad1 id=eq.1h6v.s5.279e8c7d8f8d from=translated src=- shape=a7452e28 vocab=32085bda
-/
theorem stageExcess_erase_of_not_active (S : Finset ι) (i : ι) (t : Fin m)
    (hi : ¬ I.ActiveAt i t) :
    I.stageExcess (S.erase i) t = I.stageExcess S t := by
  rw [stageExcess, stageExcess]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hli : l = i
  · subst l
    simp [excessTerm, hi]
  · simp [excessTerm, hli]

omit [Nonempty ι] in
/-- Stage load is monotone in the set of cheaply routed terminals.
@isnad1 id=le.1h6v.s5.4eb290540cd1 from=translated src=- shape=574b90e9 vocab=8b1dc393
-/
theorem stageLoad_mono {S T : Finset ι} (hST : S ⊆ T) (t : Fin m) :
    I.stageLoad S t ≤ I.stageLoad T t := by
  have hS := I.stageLoad_sub_stageX S t
  have hT := I.stageLoad_sub_stageX T t
  linarith [I.stageExcess_mono hST t]

/-- **Lemma 6.2, monotonicity.** Subsets of admissible cheap-routing sets are
admissible. Private expensive exits cause no exception because they are
automatically safe.
@isnad1 id=admissib.2h5v.s5.98cdad25a961 from=translated src=- shape=9209258a vocab=e0ca86a5
-/
theorem admissible_mono {S T : Finset ι} (hST : S ⊆ T)
    (hT : I.Admissible T) : I.Admissible S := by
  rw [I.admissible_iff_stage] at hT ⊢
  intro t
  exact le_trans (I.stageLoad_mono hST t) (hT t)

omit [Nonempty ι] in
/-- Stage excess is bounded by the total demand routed cheaply.
@isnad1 id=le.0h5v.s5.5945c046d32a from=translated src=- shape=97412362 vocab=30cbafb9
-/
theorem stageExcess_le_routedDemand (S : Finset ι) (t : Fin m) :
    I.stageExcess S t ≤ ∑ i ∈ S, I.d i := by
  rw [stageExcess]
  calc
    (∑ i, I.excessTerm S t i) ≤
        ∑ i, if i ∈ S then I.d i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases ha : I.ActiveAt i t <;> by_cases hi : i ∈ S
      · simp only [excessTerm, ha, hi, ite_true]
        linarith [I.f_nonneg i]
      · simp only [excessTerm, ha, hi, ite_true, ite_false]
        linarith [I.f_nonneg i]
      · simp only [excessTerm, ha, hi, ite_false, ite_true]
        exact (I.d_pos i).le
      · simp [excessTerm, ha, hi]
    _ = ∑ i ∈ S, I.d i := by simp

omit [Nonempty ι] in
/-- A coarse but useful stage bound: excess is at most the total demand of
the terminals routed cheaply.
@isnad1 id=le.0h5v.s5.3f13e7282c40 from=translated src=- shape=7cf493d2 vocab=dc315bd3
-/
theorem stageLoad_le_stageX_add_routedDemand (S : Finset ι) (t : Fin m) :
    I.stageLoad S t ≤ I.stageX t + ∑ i ∈ S, I.d i := by
  have hdiff := I.stageLoad_sub_stageX S t
  linarith [I.stageExcess_le_routedDemand S t]

/-- **Lemma 6.2.** The all-expensive routing is always admissible.
@isnad1 id=admissib.0h3v.s4.b4956b44d614 from=translated src=- shape=af3efc68 vocab=299ba466
-/
theorem admissible_empty : I.Admissible ∅ := by
  rw [I.admissible_iff_stage]
  intro t
  have h := I.stageLoad_le_stageX_add_routedDemand ∅ t
  simp only [Finset.sum_empty, add_zero] at h
  linarith [I.dmax_pos]

/-- **Lemma 6.2.** Every singleton cheap-routing set is admissible.
@isnad1 id=admissib.0h4v.s5.571d5121a60d from=translated src=- shape=1afd7ddf vocab=a3a37d83
-/
theorem admissible_singleton (i : ι) : I.Admissible {i} := by
  rw [I.admissible_iff_stage]
  intro t
  have h := I.stageLoad_le_stageX_add_routedDemand {i} t
  simp only [Finset.sum_singleton] at h
  linarith [I.d_le_dmax i]

/-- On a singleton terminal type every routing is admissible. This is the
non-vacuous one-terminal boundary case of downward monotonicity.
@isnad1 id=admissib.0h4v.s4.31fe2a1ff303 from=translated src=- shape=7add2534 vocab=7d715f65
-/
theorem admissible_of_subsingleton [Subsingleton ι] (S : Finset ι) :
    I.Admissible S := by
  rcases ‹Nonempty ι› with ⟨i⟩
  apply I.admissible_mono (T := {i}) ?_ (I.admissible_singleton i)
  intro j _
  simp [Subsingleton.elim j i]

omit [Nonempty ι] in
/-- Stage excess is bounded by the sum of the un-routed cheap fractions
`d i - f i` over the cheaply routed terminals.
@isnad1 id=le.0h5v.s5.a66b078ac038 from=translated src=- shape=44264aec vocab=9bfa70ba
-/
theorem stageExcess_le_routedRemainder (S : Finset ι) (t : Fin m) :
    I.stageExcess S t ≤ ∑ i ∈ S, (I.d i - I.f i) := by
  rw [stageExcess]
  calc
    (∑ i, I.excessTerm S t i) ≤
        ∑ i, if i ∈ S then I.d i - I.f i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases ha : I.ActiveAt i t <;> by_cases hi : i ∈ S
      · simp [excessTerm, ha, hi]
      · simp only [excessTerm, ha, hi, ite_true, ite_false]
        exact neg_nonpos.mpr (I.f_nonneg i)
      · simp only [excessTerm, ha, hi, ite_false, ite_true]
        linarith [I.f_le_d i]
      · simp [excessTerm, ha, hi]
    _ = ∑ i ∈ S, (I.d i - I.f i) := by simp

/-- A blocked pair has the strict split margin used in Lemma 6.2.
@isnad1 id=lt.2h5v.s6.8a8c46cd8d86 from=translated src=- shape=0f9e32aa vocab=a350e5eb
-/
theorem blockedPair_margin_lt {i j : ι} (hij : i ≠ j)
    (hblocked : ¬ I.Admissible {i, j}) :
    I.f i + I.f j < I.d i + I.d j - I.dmax := by
  rw [I.admissible_iff_stage] at hblocked
  push Not at hblocked
  obtain ⟨t, ht⟩ := hblocked
  have hdiff := I.stageLoad_sub_stageX {i, j} t
  have hrem := I.stageExcess_le_routedRemainder {i, j} t
  simp [hij] at hrem
  linarith

/-- A blocked pair has a violating stage in both terminals' cancellation
intervals. The interval conclusion is essential for the Helly argument in
Lemma 6.3; it follows from singleton admissibility, not from an extra model
assumption.
@isnad1 id=ex.2h5v.s6.7547455fce40 from=translated src=- shape=5cb6125c vocab=2dbeb2a8
-/
theorem blockedPair_violation_stage {i j : ι} (hij : i ≠ j)
    (hblocked : ¬ I.Admissible {i, j}) :
    ∃ t, I.stageX t + I.dmax < I.stageLoad {i, j} t ∧
      I.ActiveAt i t ∧ I.ActiveAt j t := by
  rw [I.admissible_iff_stage] at hblocked
  push Not at hblocked
  obtain ⟨t, ht⟩ := hblocked
  have hdiff := I.stageLoad_sub_stageX {i, j} t
  have hexcess : I.dmax < I.stageExcess {i, j} t := by
    linarith
  refine ⟨t, ht, ?_, ?_⟩
  · by_contra hi
    have herase := I.stageExcess_erase_of_not_active {i, j} i t hi
    have hsingle := I.stageExcess_le_routedDemand {j} t
    simp [hij] at herase
    simp only [Finset.sum_singleton] at hsingle
    linarith [I.d_le_dmax j]
  · by_contra hj
    have herase := I.stageExcess_erase_of_not_active {i, j} j t hj
    have hsingle := I.stageExcess_le_routedDemand {i} t
    have heraseFinset : ({i, j} : Finset ι).erase j = {i} := by
      calc
        ({i, j} : Finset ι).erase j = ({j, i} : Finset ι).erase j :=
          congrArg (fun S : Finset ι => S.erase j) (Finset.pair_comm i j)
        _ = {i} := Finset.erase_insert (by simpa using hij.symm)
    rw [heraseFinset] at herase
    simp only [Finset.sum_singleton] at hsingle
    linarith [I.d_le_dmax i]

omit [Nonempty ι] in
/-- If every terminal is active at a stage, the excess of a two-terminal
cheap routing contains the negative cheap-flow contribution of every
terminal.
@isnad1 id=eq.2h6v.s6.82c883889cbb from=translated src=- shape=54af2ed9 vocab=4c7cc162
-/
theorem stageExcess_pair_eq_fullSum {i j : ι} (hij : i ≠ j) (t : Fin m)
    (hall : ∀ l, I.ActiveAt l t) :
    I.stageExcess {i, j} t =
      I.d i + I.d j - ∑ l, I.f l := by
  rw [stageExcess]
  calc
    (∑ l, I.excessTerm {i, j} t l) =
        ∑ l, (-I.f l + if l ∈ ({i, j} : Finset ι) then I.d l else 0) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l ∈ ({i, j} : Finset ι)
      · simp only [excessTerm, hall l, hl, ite_true]
        linarith
      · simp [excessTerm, hall l, hl]
    _ = I.d i + I.d j - ∑ l, I.f l := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_filter]
      have hfilter :
          Finset.univ.filter (fun l => l ∈ ({i, j} : Finset ι)) = {i, j} := by
        ext l
        simp
      rw [hfilter, Finset.sum_pair hij]
      rw [Finset.sum_neg_distrib]
      linarith

/-- A fully active violating pair gives all of the numerical conclusions of
Lemma 6.3. The first equality records the full aggregation, while the
remaining conjuncts are its strict margin and demand bounds.
@isnad1 id=and.3h6v.s8.1486701a7d33 from=translated src=- shape=efcab4bb vocab=0b565d19
-/
theorem fullAggregation_bounds {i j : ι} (hij : i ≠ j) (t : Fin m)
    (hviolate : I.stageX t + I.dmax < I.stageLoad {i, j} t)
    (hall : ∀ l, I.ActiveAt l t) :
    I.stageExcess {i, j} t =
        I.d i + I.d j - ∑ l, I.f l ∧
      (∑ l, I.f l) < I.d i + I.d j - I.dmax ∧
      I.d i + I.d j - I.dmax ≤ min (I.d i) (I.d j) ∧
      min (I.d i) (I.d j) ≤ I.dmax := by
  have hagg := I.stageExcess_pair_eq_fullSum hij t hall
  have hdiff := I.stageLoad_sub_stageX {i, j} t
  refine ⟨hagg, ?_, ?_, ?_⟩
  · linarith
  · apply le_min
    · linarith [I.d_le_dmax j]
    · linarith [I.d_le_dmax i]
  · exact (min_le_left (I.d i) (I.d j)).trans (I.d_le_dmax i)

/-- **Lemma 6.3 (Helly full aggregation).** For a finite chain with at least
two terminals, if every distinct pair is blocked, some blocked pair has a
violating stage in every terminal's cancellation interval. At that stage the
pair constraint aggregates the cheap flow of every terminal and yields the
strict full-sum inequality and both demand bounds from the paper.
@isnad1 id=ex.1h3v.s8.0ef06e14c68f from=translated src=- shape=11e832ac vocab=9a51b1d5
-/
theorem helly_full_aggregation [Nontrivial ι]
    (hblocked : ∀ i j, i ≠ j → ¬ I.Admissible {i, j}) :
    ∃ i j t, i ≠ j ∧
      ¬ I.Admissible {i, j} ∧
      I.stageX t + I.dmax < I.stageLoad {i, j} t ∧
      (∀ l, I.ActiveAt l t) ∧
      I.stageExcess {i, j} t =
          I.d i + I.d j - ∑ l, I.f l ∧
      (∑ l, I.f l) < I.d i + I.d j - I.dmax ∧
      I.d i + I.d j - I.dmax ≤ min (I.d i) (I.d j) ∧
      min (I.d i) (I.d j) ≤ I.dmax := by
  obtain ⟨r, -, hr⟩ := Finset.exists_max_image Finset.univ
    (fun l => (I.e l).val) Finset.univ_nonempty
  obtain ⟨q, -, hq⟩ := Finset.exists_min_image Finset.univ
    (fun l => (I.p l).val) Finset.univ_nonempty
  by_cases hqr : q = r
  · subst r
    obtain ⟨j, hjq⟩ := exists_ne q
    have hqj : q ≠ j := Ne.symm hjq
    have hqjBlocked := hblocked q j hqj
    obtain ⟨t, hviolate, hqActive, -⟩ :=
      I.blockedPair_violation_stage hqj hqjBlocked
    have hall : ∀ l, I.ActiveAt l t := by
      intro l
      exact ⟨(hr l (Finset.mem_univ l)).trans hqActive.1,
        hqActive.2.trans_le (hq l (Finset.mem_univ l))⟩
    obtain ⟨hagg, hsum, hmin, hminD⟩ :=
      I.fullAggregation_bounds hqj t hviolate hall
    exact ⟨q, j, t, hqj, hqjBlocked, hviolate, hall,
      hagg, hsum, hmin, hminD⟩
  · have hqrBlocked := hblocked q r hqr
    obtain ⟨t, hviolate, hqActive, hrActive⟩ :=
      I.blockedPair_violation_stage hqr hqrBlocked
    have hall : ∀ l, I.ActiveAt l t := by
      intro l
      exact ⟨(hr l (Finset.mem_univ l)).trans hrActive.1,
        hqActive.2.trans_le (hq l (Finset.mem_univ l))⟩
    obtain ⟨hagg, hsum, hmin, hminD⟩ :=
      I.fullAggregation_bounds hqr t hviolate hall
    exact ⟨q, r, t, hqr, hqrBlocked, hviolate, hall,
      hagg, hsum, hmin, hminD⟩

private theorem ratio_sum_lt_one_of_sum_lt_both {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxa : x + y < a) (hxb : x + y < b) :
    x / a + y / b < 1 := by
  rcases le_total a b with hab | hba
  · have hmul : y * a ≤ y * b := mul_le_mul_of_nonneg_left hab hy
    have hstrict : (x + y) * b < a * b :=
      mul_lt_mul_of_pos_right hxa hb
    have hnum : x * b + y * a < a * b := by
      nlinarith
    rw [show x / a + y / b = (x * b + y * a) / (a * b) by
      field_simp]
    exact (div_lt_one (mul_pos ha hb)).2 hnum
  · have hmul : x * b ≤ x * a := mul_le_mul_of_nonneg_left hba hx
    have hstrict : (x + y) * a < b * a :=
      mul_lt_mul_of_pos_right hxb ha
    have hnum : x * b + y * a < a * b := by
      nlinarith
    rw [show x / a + y / b = (x * b + y * a) / (a * b) by
      field_simp]
    exact (div_lt_one (mul_pos ha hb)).2 hnum

/-- **Lemma 6.2, blocked-pair fraction bound (strict form).** A blocked pair
has cheap fractions summing strictly below one.
@isnad1 id=lt.2h5v.s6.65b49f38faec from=translated src=- shape=9ca4b403 vocab=a2639ffa
-/
theorem blockedPair_cheapFraction_lt_one {i j : ι} (hij : i ≠ j)
    (hblocked : ¬ I.Admissible {i, j}) :
    I.f i / I.d i + I.f j / I.d j < 1 := by
  have hm := I.blockedPair_margin_lt hij hblocked
  have hiD := I.d_le_dmax i
  have hjD := I.d_le_dmax j
  apply ratio_sum_lt_one_of_sum_lt_both
      (I.d_pos i) (I.d_pos j) (I.f_nonneg i) (I.f_nonneg j)
  · linarith
  · linarith

/-- The paper's stated closed form `z_i + z_j ≤ 1`.
@isnad1 id=le.2h5v.s6.7c4cf6bd4381 from=translated src=- shape=9ca4b403 vocab=d15c9a7e
-/
theorem blockedPair_cheapFraction_le_one {i j : ι} (hij : i ≠ j)
    (hblocked : ¬ I.Admissible {i, j}) :
    I.f i / I.d i + I.f j / I.d j ≤ 1 :=
  (I.blockedPair_cheapFraction_lt_one hij hblocked).le

/-- Equivalent expensive-fraction form: a blocked pair has
`1 < a_i + a_j`.
@isnad1 id=lt.2h5v.s7.126583d80a0c from=translated src=- shape=3e2b5f93 vocab=fd5f0c5e
-/
theorem one_lt_blockedPair_expensiveFraction {i j : ι} (hij : i ≠ j)
    (hblocked : ¬ I.Admissible {i, j}) :
    1 < (1 - I.f i / I.d i) + (1 - I.f j / I.d j) := by
  linarith [I.blockedPair_cheapFraction_lt_one hij hblocked]

/-- Closed expensive-fraction form `1 ≤ a_i + a_j`.
@isnad1 id=le.2h5v.s7.e49a83551665 from=translated src=- shape=3e2b5f93 vocab=f25ed3ae
-/
theorem one_le_blockedPair_expensiveFraction {i j : ι} (hij : i ≠ j)
    (hblocked : ¬ I.Admissible {i, j}) :
    1 ≤ (1 - I.f i / I.d i) + (1 - I.f j / I.d j) :=
  (I.one_lt_blockedPair_expensiveFraction hij hblocked).le

end Instance
end Chain
end Goemans
