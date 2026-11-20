/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Tengoku
public import Tengoku.Kostkanumbers.KostkaNumbers.Dominate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Prove some results about when small lists dominate one another.  Used for some of the computations.
-/

public section namespace Tengoku.Kostkanumbers end Tengoku.Kostkanumbers open Tengoku.Kostkanumbers
local notation L " ⊵ " L' => Dominates L L'
local notation L " ⊴ " L' => Dominates L' L


/--
@isnad1 id=iff.0h2v.s4.eaf430dbc329 from=translated src=- shape=30c570b9 vocab=be7e39b4
-/
lemma _root_.Tengoku.Kostkanumbers.singleton_dominates_singleton {a b : ℕ} : ([a] ⊴ [b]) ↔ a ≤ b := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp [h]

/--
@isnad1 id=iff.0h3v.s5.dc6c4a429aae from=translated src=- shape=742324d2 vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.singleton_dominates_pair {a b c : ℕ} : ([a, b] ⊴ [c]) ↔ a + b ≤ c := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h] <;> lia

/--
@isnad1 id=iff.0h4v.s5.81b1a3652eb3 from=translated src=- shape=ebefb0e1 vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.singleton_dominates_triple {a b c d : ℕ} : ([a, b, c] ⊴ [d]) ↔ a + b + c ≤ d := by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa [← add_assoc] using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h] <;> lia

/--
@isnad1 id=iff.0h3v.s4.06197c7fd62b from=translated src=- shape=9a1b3699 vocab=be7e39b4
-/
lemma _root_.Tengoku.Kostkanumbers.pair_dominates_singleton {a b c : ℕ} : ([a] ⊴ [b, c]) ↔ a ≤ b := by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]

/--
@isnad1 id=iff.0h4v.s5.db61742fef45 from=translated src=- shape=43e3b8ba vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.pair_dominates_pair {a b c d : ℕ} : ([a, b] ⊴ [c, d]) ↔ a ≤ c ∧ a + b ≤ c + d := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa using h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h₁, h₂]

/--
@isnad1 id=iff.0h5v.s6.3d7634e68cd8 from=translated src=- shape=2dcc23cf vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.pair_dominates_triple {a b c d e : ℕ} : ([a, b, c] ⊴ [d, e]) ↔
    a ≤ d ∧ a + b + c ≤ d + e := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa [add_assoc] using h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂] <;> lia

/--
@isnad1 id=iff.0h4v.s4.70c90bdbd02b from=translated src=- shape=b8b41445 vocab=be7e39b4
-/
lemma _root_.Tengoku.Kostkanumbers.triple_dominates_singleton {a b c d : ℕ} : ([a] ⊴ [b, c, d]) ↔ a ≤ b := by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]

/--
@isnad1 id=iff.0h5v.s5.733d9e61b42c from=translated src=- shape=56fc6976 vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.triple_dominates_pair {a b c d e : ℕ} : ([a, b] ⊴ [c, d, e]) ↔
    a ≤ c ∧ a + b ≤ c + d := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂]

/--
@isnad1 id=iff.0h6v.s6.7ce357fa13cf from=translated src=- shape=8d6c2885 vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.triple_dominates_triple {a b c d e f : ℕ} : ([a, b, c] ⊴ [d, e, f]) ↔
    a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f := by
  constructor
  · intro h
    constructor; swap; constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa [← add_assoc] using h
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂, h₃]

/--
@isnad1 id=iff.0h7v.s6.712b50b45cc3 from=translated src=- shape=a3c50b59 vocab=4250c09b
-/
lemma _root_.Tengoku.Kostkanumbers.quad_dominates_triple {a b c d e f g : ℕ} : ([a, b, c] ⊴ [d, e, f, g]) ↔
    a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f := by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_three_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, Fin.sum_univ_four, h₁, h₂, h₃]
-- Tengoku: root names of this library moved to Tengoku.Kostkanumbers so they do not collide with other libraries (generated)
