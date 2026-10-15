/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/
module

public import Tengoku.LeanPool.LeanPool.PumpingCfg.ChomskyNormalForm.ContextFreeGrammarExtras

/-!
# Empty Elimination

This file contains the algorithm to eliminate rules from a context-free grammar which rewrite to
the empty string, while preserving the language of the grammar (except the empty string).

## Main definitions
* `ContextFreeGrammar.computeNullables`: Fixpoint iteration to compute all nonterminals from which
  `g` can derive the empty string.
* `ContextFreeGrammar.eliminateEmpty`: Eliminates all rules which rewrite to the empty string.

## Main theorems
* `ContextFreeGrammar.computeNullables_iff`: All and only nullable symbols are computed.
* `ContextFreeGrammar.eliminateEmpty_correct`: The transformed grammar's language coincides with the
original up to omission of the empty word.

## References
* [John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman. 2006. Introduction to Automata Theory,
   Languages, and Computation (3rd Edition). Addison-Wesley Longman Publishing Co., Inc., USA.]
   [Hopcroft et al. 2006]
-/

@[expose] public section

namespace ContextFreeRule
universe uT uN

variable {T : Type uT} {N : Type uN}

/--
@isnad1 id=eq.1h4v.s5.201c70a05776 from=translated src=- shape=856fa5c8 vocab=7187f11e
-/
lemma Rewrites.empty {u : List (Symbol T N)} {r : ContextFreeRule T N}
    (hu : r.Rewrites u []) :
    r.output = [] := by
  obtain ⟨_, _, -, _⟩ := hu.exists_parts
  simp_all

end ContextFreeRule

namespace ContextFreeGrammar

universe uT uN
variable {T : Type uT}

/-! Properties of context-free transformations to the empty string. -/
section NullableDerivations

variable {g : ContextFreeGrammar T}

/-- A nonterminal is nullable if it can be transformed into the empty string -/
abbrev NullableNonTerminal (n : g.NT) : Prop := g.Derives [Symbol.nonterminal n] []

/-- A word is nullable if it can be transformed into the empty string -/
abbrev NullableWord (u : List (Symbol T g.NT)) : Prop := g.Derives u []

private lemma DerivesIn.empty_of_append_left_aux {u v w : List (Symbol T g.NT)} {m : ℕ}
    (hwm : g.DerivesIn w [] m) (hw : w = u ++ v) :
    ∃ k ≤ m, g.DerivesIn u [] k := by
  induction hwm using DerivesIn.head_induction_on generalizing u v with
  | refl =>
    rw [List.nil_eq_append_iff] at hw
    rw [hw.left]
    exact ⟨0, Nat.le_refl 0, DerivesIn.zero_steps []⟩
  | head huv _ ih =>
    obtain ⟨r, hrg, hr⟩ := huv
    obtain ⟨p, q, heq₁, heq₂⟩ := ContextFreeRule.Rewrites.exists_parts hr
    rw [hw, List.append_assoc, List.append_eq_append_iff] at heq₁
    cases heq₁ with
    | inl hpv =>
      obtain ⟨x', hp, _⟩ := hpv
      obtain ⟨m', _, _⟩ := @ih u (x' ++ r.output ++ q) (by simp [heq₂, hp])
      use m'
      tauto
    | inr huq =>
      obtain ⟨x', hu, hr⟩ := huq
      cases x' with
      | nil =>
        obtain ⟨m', _, _⟩ := @ih u (r.output ++ q) (by simp [heq₂, hu])
        use m'
        tauto
      | cons h t =>
        obtain ⟨_, _⟩ := hr
        rw [List.append_eq, ← List.append_assoc] at heq₂
        obtain ⟨m', hm, hd⟩ := ih heq₂
        refine ⟨m'.succ, Nat.succ_le_succ hm, Produces.trans_derivesIn ⟨r, hrg, ?_⟩ hd⟩
        rw [ContextFreeRule.rewrites_iff]
        exact ⟨p, t, List.append_assoc .. ▸ hu, rfl⟩

/--
@isnad1 id=ex.1h5v.s6.baf14dc8d4a4 from=translated src=- shape=a49d97ea vocab=a15f8172
-/
lemma DerivesIn.empty_of_append_left {m : ℕ} {u v : List (Symbol T g.NT)}
    (huv : g.DerivesIn (u ++ v) [] m) :
    ∃ k ≤ m, g.DerivesIn u [] k := by
  apply empty_of_append_left_aux <;> tauto

/--
@isnad1 id=ex.2h6v.s6.e8d98a50f753 from=translated src=- shape=9b80a081 vocab=a15f8172
-/
lemma DerivesIn.empty_of_append_right_aux {u v w : List (Symbol T g.NT)} {m : ℕ}
    (hwm : g.DerivesIn w [] m) (hw : w = u ++ v) :
    ∃ k ≤ m, g.DerivesIn v [] k := by
  induction hwm using DerivesIn.head_induction_on generalizing u v with
  | refl =>
    rw [List.nil_eq_append_iff] at hw
    rw [hw.right]
    exact ⟨0, Nat.le_refl 0, DerivesIn.zero_steps []⟩
  | head hp _ ih =>
    obtain ⟨r, hrg, hr⟩ := hp
    obtain ⟨p, q, heq₁, heq₂⟩ := hr.exists_parts
    rw [hw, List.append_assoc, List.append_eq_append_iff] at heq₁
    cases heq₁ with
    | inl hpv =>
      obtain ⟨y', heq₁ , hy⟩ := hpv
      rw [heq₁, List.append_assoc, List.append_assoc] at heq₂
      obtain ⟨m', hm, hd⟩ := ih heq₂
      refine ⟨m'.succ, Nat.succ_le_succ hm, ?_⟩
      apply Produces.trans_derivesIn
      · use r, hrg
        rw [ContextFreeRule.rewrites_iff]
        exact ⟨y', q, List.append_assoc .. ▸ hy, rfl⟩
      · simp [hd]
    | inr huq =>
      obtain ⟨q', _, hq⟩ := huq
      cases q' with
      | nil =>
        rw [List.append_assoc] at heq₂
        rw [List.singleton_append, List.nil_append] at hq
        obtain ⟨m', hm, hd⟩ := ih heq₂
        use m'.succ, Nat.succ_le_succ hm
        apply Produces.trans_derivesIn _ hd
        use r, hrg
        rw [ContextFreeRule.rewrites_iff]
        exact ⟨[], q, hq.symm, rfl⟩
      | cons _ t =>
        obtain ⟨_, _⟩ := hq
        rw [List.append_eq, List.append_assoc] at heq₂
        repeat rw [← List.append_assoc] at heq₂
        obtain ⟨m', hm, hv⟩ := ih heq₂
        exact ⟨m', Nat.le_succ_of_le hm, hv⟩

/--
@isnad1 id=ex.1h5v.s6.41a276b8ddc6 from=translated src=- shape=adb6df6e vocab=a15f8172
-/
lemma DerivesIn.empty_of_append_right {m : ℕ} {u v : List (Symbol T g.NT)}
    (huv : g.DerivesIn (u ++ v) [] m) :
    ∃ k ≤ m, g.DerivesIn v [] k := by
  apply empty_of_append_right_aux <;> tauto

/--
@isnad1 id=ex.1h6v.s6.808e3f332b37 from=translated src=- shape=ed7a046d vocab=a15f8172
-/
lemma DerivesIn.empty_of_append {u v w : List (Symbol T g.NT)} {m : ℕ}
    (huvw : g.DerivesIn (u ++ v ++ w) [] m) :
    ∃ k ≤ m, g.DerivesIn v [] k := by
  obtain ⟨m₁, hm₁n, huv⟩ := huvw.empty_of_append_left
  obtain ⟨m₂, hm₂n, hv⟩ := huv.empty_of_append_right
  exact ⟨m₂, Nat.le_trans hm₂n hm₁n, hv⟩

/--
@isnad1 id=nullable.1h5v.s6.546aae685477 from=translated src=- shape=e896b629 vocab=1c5d2af8
-/
lemma NullableWord.empty_of_append {u v w : List (Symbol T g.NT)}
    (huvw : NullableWord (u ++ v ++ w)) :
    NullableWord v := by
  unfold NullableWord at *
  rw [derives_iff_derivesIn] at huvw ⊢
  obtain ⟨n, hn⟩ := huvw
  obtain ⟨m, _, _⟩ := hn.empty_of_append
  use m

/--
@isnad1 id=nullable.1h4v.s5.37bebf22f553 from=translated src=- shape=ace273eb vocab=1c5d2af8
-/
lemma NullableWord.empty_of_append_left {u v : List (Symbol T g.NT)} (huv : NullableWord (u ++ v)) :
    NullableWord u := @NullableWord.empty_of_append _ _ [] _ _ huv

/--
@isnad1 id=nullable.1h4v.s5.55cf9d27d360 from=translated src=- shape=1e3eca72 vocab=1c5d2af8
-/
lemma NullableWord.empty_of_append_right {u v : List (Symbol T g.NT)}
    (huv : NullableWord (u ++ v)) : NullableWord v := by
  apply NullableWord.empty_of_append
  · rw [List.append_nil]
    exact huv

/--
@isnad1 id=ex.2h5v.s6.08e2510af0fc from=translated src=- shape=fa9f0272 vocab=4c4766f2
-/
lemma DerivesIn.mem_nullable {u : List (Symbol T g.NT)} {s : Symbol T g.NT} {m : ℕ}
    (hu : g.DerivesIn u [] m) (hsu : s ∈ u) :
    ∃ k ≤ m, g.DerivesIn [s] [] k := by
  induction u generalizing m with
  | nil => contradiction
  | cons a l ih =>
    cases hsu with
    | head =>
      exact hu.empty_of_append_left
    | tail _ hs =>
      change g.DerivesIn ([a] ++ l) [] m at hu
      obtain ⟨m, hmn, hte⟩ := hu.empty_of_append_right
      obtain ⟨m', hmm, hse⟩ := ih hte hs
      exact ⟨m', hmm.trans hmn, hse⟩

/--
@isnad1 id=derives.2h6v.s6.1f41eae1c64d from=translated src=- shape=6c5d934c vocab=f965c82b
-/
lemma Derives.append_left_trans {u v w x : List (Symbol T g.NT)} (huv : g.Derives u v)
    (hwx : g.Derives w x) :
    g.Derives (w ++ u) (x ++ v) := (huv.append_left _).trans (hwx.append_right _)

/--
@isnad1 id=not.0h4v.s4.56174e13dfa8 from=translated src=- shape=de29f93e vocab=2ee270ee
-/
lemma NullableWord.cons_terminal {t : T} {u : List (Symbol T g.NT)} :
    ¬ NullableWord (Symbol.terminal t :: u) := by
  by_contra htu
  change g.Derives ([Symbol.terminal t] ++ u) [] at htu
  cases (NullableWord.empty_of_append_left htu).eq_or_head with
  | inl => contradiction
  | inr hv =>
    obtain ⟨_, ⟨_, _, ht⟩, _⟩ := hv
    cases ht with
    | cons _ hts =>
      cases hts

/--
@isnad1 id=eq.1h3v.s5.1628f37bf00f from=translated src=- shape=062f58b8 vocab=c6aa6037
-/
lemma Derives.of_empty {u : List (Symbol T g.NT)} (hu : g.Derives [] u) : u = [] := by
  induction hu with
  | refl => rfl
  | tail _ hp _ =>
    obtain ⟨_, _, hr⟩ := hp
    cases hr <;> contradiction

/--
@isnad1 id=nullable.1h3v.s6.fcf852d1bdf1 from=translated src=- shape=b5c0f879 vocab=6cac9db0
-/
lemma symbols_nullable_nullableWord (u : List (Symbol T g.NT)) (hu : ∀ a ∈ u, g.Derives [a] []) :
    NullableWord u := by
  induction u with
  | nil => rfl
  | cons a l ih =>
    change g.Derives ([a] ++ l) []
    trans
    · apply Derives.append_right
      exact hu _ List.mem_cons_self
    · simp_all

/--
@isnad1 id=ex.2h5v.s6.b2f44a3c16a5 from=translated src=- shape=0fce0772 vocab=2b44d05b
-/
lemma DerivesIn.nullable_mem_nonterminal {u : List (Symbol T g.NT)} {s : Symbol T g.NT} {m : ℕ}
    (hu : g.DerivesIn u [] m) (hsu : s ∈ u) :
    ∃ n, s = Symbol.nonterminal n := by
  have ⟨m, _, hsm⟩ := hu.mem_nullable hsu
  cases m with
  | zero => contradiction
  | succ m =>
    obtain ⟨_, hp, _⟩ := hsm.head_of_succ
    obtain ⟨r, _, hsu⟩ := hp
    obtain ⟨p, q, hs, -⟩ := hsu.exists_parts
    cases p <;> simp at hs
    cases q <;> simp at hs
    use r.input

/--
@isnad1 id=ex.2h4v.s6.731654374799 from=translated src=- shape=936ee8c9 vocab=ea17e541
-/
lemma NullableWord.nullableNonTerminal {u : List (Symbol T g.NT)} {s : Symbol T g.NT}
    (hu : NullableWord u) (hsu : s ∈ u) :
    ∃ n, s = Symbol.nonterminal n ∧ NullableNonTerminal n := by
  induction u generalizing s with
  | nil => contradiction
  | cons a l ih =>
    cases hsu with
    | head =>
      cases a with
      | terminal => exact hu.cons_terminal.elim
      | nonterminal n => exact ⟨n, rfl, hu.empty_of_append_left⟩
    | tail _ hsu =>
      apply ih _ hsu
      exact NullableWord.empty_of_append_right (u := [a]) hu

end NullableDerivations

/-! Definition and properties of `ContextFreeGrammar.NullableRelated u v` which relates strings,
which are equal up to nullable symbols. -/
section NullableRelated

variable {g : ContextFreeGrammar T}

/-- `NullableRelated u v` means that `v` and `u` are equal up to interspersed nonterminals, each of
 which can be transformed to the empty string (i.e. for each additional nonterminal `nt`,
 `NullableNonterminal nt` holds) -/
inductive NullableRelated : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  /-- The empty string is `NullableRelated` to any `w`, s.t., `NullableWord w` -/
  | empty_left (u : List (Symbol T g.NT)) (hu : NullableWord u) : NullableRelated [] u
  /-- A terminal symbol `t` needs to be matched exactly -/
  | cons_term {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) (t : T) :
                      NullableRelated (Symbol.terminal t :: u) (Symbol.terminal t :: v)
  /-- A nonterminal symbol `n` can be matched exactly -/
  | cons_nterm_match {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) (n : g.NT) :
                     NullableRelated (Symbol.nonterminal n :: u) (Symbol.nonterminal n :: v)
  /-- A nonterminal symbol `n`, s.t., `NullableNonterminal n` on the right, need not be matched -/
  | cons_nterm_nullable {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) {n : g.NT}
                        (hn : NullableNonTerminal n) : NullableRelated u (Symbol.nonterminal n :: v)

/--
@isnad1 id=nullable.0h3v.s4.311c3494889f from=translated src=- shape=2f53d348 vocab=8d1b2150
-/
@[refl]
lemma NullableRelated.refl (u : List (Symbol T g.NT)) : NullableRelated u u := by
  induction u with
  | nil => exact empty_left [] (by rfl)
  | cons d _ ih => cases d <;> constructor <;> exact ih

/--
@isnad1 id=derives.1h4v.s4.01d86c52c331 from=translated src=- shape=9d1c27f3 vocab=c9c3607e
-/
lemma NullableRelated.derives {u v : List (Symbol T g.NT)} (huv : NullableRelated u v) :
    g.Derives v u := by
  induction huv with
  | empty_left _ hw => exact hw
  | cons_term _ t ih => exact List.singleton_append .. ▸ ih.append_left _
  | cons_nterm_match _ _ ih =>
    nth_rewrite 2 [← List.singleton_append]
    rw [← List.singleton_append]
    exact ih.append_left _
  | cons_nterm_nullable _ hnt ih =>
    rw [← List.singleton_append]
    exact ih.append_left_trans hnt

/--
@isnad1 id=nullable.1h3v.s4.6b454659ecb4 from=translated src=- shape=05940375 vocab=24a79297
-/
lemma NullableRelated.empty_nullableWord {u : List (Symbol T g.NT)} (hu : NullableRelated [] u) :
    NullableWord u := by
  induction u with
  | nil => rfl
  | cons _ l ih => cases hu with
    | empty_left _ hsl => exact hsl
    | cons_nterm_nullable hl hn => exact (hn.append_right l).trans (ih hl)

/--
@isnad1 id=eq.1h3v.s5.b78e2168c815 from=translated src=- shape=c2743f23 vocab=424a3ce3
-/
lemma NullableRelated.empty_right {u : List (Symbol T g.NT)} (hu : NullableRelated u []) :
    u = [] := by
  cases hu
  rfl

/--
@isnad1 id=nullable.2h5v.s6.df708f0e261b from=translated src=- shape=84943de5 vocab=fc856c8a
-/
lemma NullableRelated.append_nullable_left {u v w : List (Symbol T g.NT)}
    (huv : NullableRelated u v) (hw : NullableWord w) :
    NullableRelated u (w ++ v) := by
  induction w generalizing u v with
  | nil => exact huv
  | cons a l ih =>
    rw [← List.singleton_append] at hw
    obtain ⟨_, rfl, hnt⟩ := hw.nullableNonTerminal List.mem_cons_self
    exact NullableRelated.cons_nterm_nullable (ih huv hw.empty_of_append_right) hnt

/--
@isnad1 id=nullable.2h6v.s6.33f4408dfa5f from=translated src=- shape=d9f63012 vocab=0f4d5ff8
-/
lemma nullable_related_append {u₁ u₂ v₁ v₂ : List (Symbol T g.NT)}
    (hv : NullableRelated v₁ v₂) (hu : NullableRelated u₁ u₂) :
    NullableRelated (v₁ ++ u₁) (v₂ ++ u₂) := by
  induction hv with
  | empty_left v₂ hv => exact hu.append_nullable_left hv
  | cons_term _ t ih => exact NullableRelated.cons_term ih t
  | cons_nterm_match _ n ih => exact NullableRelated.cons_nterm_match ih n
  | cons_nterm_nullable _ hnt ih => exact NullableRelated.cons_nterm_nullable ih hnt

/--
@isnad1 id=ex.1h5v.s7.5d6c9813dc5b from=translated src=- shape=0010b5d2 vocab=0f4d5ff8
-/
lemma NullableRelated.append_split {u v w : List (Symbol T g.NT)}
    (huvw : NullableRelated u (v ++ w)) :
    ∃ v' w', u = v' ++ w' ∧ NullableRelated v' v ∧ NullableRelated w' w := by
  induction v generalizing u w with
  | nil =>
    exact ⟨[], u, rfl, refl [], huvw⟩
  | cons a l ih =>
    cases u with
    | nil =>
      use [], [], rfl
      have hvw : NullableRelated [] (l ++ w) := by
        constructor
        rw [← List.singleton_append, List.append_assoc] at huvw
        exact NullableWord.empty_of_append_right huvw.empty_nullableWord
      obtain ⟨_, _, heq, _, hw⟩ := ih hvw
      constructor
      · constructor
        cases huvw
        · apply NullableWord.empty_of_append_left
          assumption
        · change NullableWord ([Symbol.nonterminal _] ++ l)
          apply Derives.trans
          · apply Derives.append_right
            assumption
          · exact hvw.empty_nullableWord.empty_of_append_left
      · simp_all
    | cons sᵤ u =>
      cases huvw with
      | cons_term huvw t =>
        obtain ⟨v', w', hu, hv', hw'⟩ := ih huvw
        exact ⟨Symbol.terminal t :: v', w', List.cons_eq_cons.2 ⟨rfl, hu⟩,
          ⟨NullableRelated.cons_term hv' t, hw'⟩⟩
      | cons_nterm_match huvw n =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        exact ⟨Symbol.nonterminal n :: v', w', List.cons_eq_cons.2 ⟨rfl, huv'w'⟩,
          ⟨NullableRelated.cons_nterm_match hv'v n, hw'w⟩⟩
      | cons_nterm_nullable huvw hnt =>
        obtain ⟨v', w', huv'w', hv'v, hw'w⟩ := ih huvw
        exact ⟨v', w', huv'w', cons_nterm_nullable hv'v hnt, hw'w⟩

/--
@isnad1 id=ex.1h6v.s7.60bc03f855d5 from=translated src=- shape=2da34aba vocab=0f4d5ff8
-/
lemma NullableRelated.append_split_three {u v w x : List (Symbol T g.NT)}
    (huvwx : NullableRelated u (v ++ w ++ x)) :
    ∃ u₁ u₂ u₃ : List (Symbol T g.NT),
      u = u₁ ++ u₂ ++ u₃ ∧ NullableRelated u₁ v ∧ NullableRelated u₂ w ∧ NullableRelated u₃ x := by
  obtain ⟨u', u₃, huu'u₃, hu'vw, hu₃x⟩ := huvwx.append_split
  obtain ⟨u₁, u₂, hu'u₁u₂, hu₁v, hu₂w⟩ := hu'vw.append_split
  exact ⟨u₁, u₂, u₃, hu'u₁u₂ ▸ huu'u₃, hu₁v, hu₂w, hu₃x⟩

end NullableRelated

/-! Definition an properties of `ContextFreeGrammar.ComputeNullables` computing the nullable
nonterminals of a grammar `g`, i.e., those symbols which can be transformed to the empty string. -/
section ComputeNullables

variable {N : Type uN} [DecidableEq N]

/-- Check if a symbol is nullable (w.r.t. to set of nullable symbols `p`), i.e.,
 `symbol_is_nullable p s` only holds if `s` is a nonterminal and it is in `p` -/
def symbolIsNullable (p : Finset N) (s : Symbol T N) : Bool :=
  match s with
  | Symbol.terminal _ => False
  | Symbol.nonterminal n => n ∈ p

/-- A rule is nullable if all output symbols are nullable -/
def ruleIsNullable (p : Finset N) (r : ContextFreeRule T N) : Bool :=
  ∀ s ∈ r.output, symbolIsNullable p s

/-- Add the input of a rule as a nullable symbol to `p` if the rule is nullable -/
def addIfNullable (r : ContextFreeRule T N) (p : Finset N) : Finset N :=
  if ruleIsNullable p r then insert r.input p else p

/--
@isnad1 id=le.0h4v.s5.f1ce7e491bfe from=translated src=- shape=3af6b3e3 vocab=aaf31284
-/
lemma subset_addIfNullable (r : ContextFreeRule T N) (p : Finset N) :
    p ⊆ (addIfNullable r p) := by
  unfold addIfNullable
  split <;> simp

variable {g : ContextFreeGrammar T} [DecidableEq g.NT]

/-- `generators g` is the set of nonterminals that appear in the left hand side of rules of `g` -/
noncomputable def generators (g : ContextFreeGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  (g.rules.toList.map ContextFreeRule.input).toFinset

/--
@isnad1 id=mem.1h3v.s6.c22e3c33d747 from=translated src=- shape=ea66e294 vocab=d5aa776e
-/
lemma input_mem_generators {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules) :
    r.input ∈ g.generators := by
  unfold generators
  rw [← Finset.mem_toList] at hrg
  revert hrg
  induction g.rules.toList with
  | nil => simp
  | cons _ _ ih =>
    simp only [List.mem_toFinset, List.mem_map, List.mem_cons, List.map_cons, List.toFinset_cons,
      Finset.mem_insert] at ih ⊢
    rintro (c1 | c2)
    · simp_all
    · simp_all

/--
@isnad1 id=le.2h4v.s6.795dd126dc56 from=translated src=- shape=5871536a vocab=a10799cd
-/
lemma addIfNullable_subset_generators {r : ContextFreeRule T g.NT} {p : Finset g.NT}
    (hpg : p ⊆ g.generators) (hrg : r ∈ g.rules) :
    addIfNullable r p ⊆ g.generators := by
  unfold addIfNullable
  split
  · exact Finset.insert_subset (input_mem_generators hrg) hpg
  · exact hpg

/-- Single round of fixpoint iteration; adds `r.input` to the set of nullable symbols if all symbols
in `r.output` are nullable -/
noncomputable def addNullables (p : Finset g.NT) : Finset g.NT :=
  g.rules.toList.attach.foldr (fun ⟨r, _⟩ ↦ addIfNullable r) p

/--
@isnad1 id=le.1h3v.s6.f253e43f29b7 from=translated src=- shape=86897a44 vocab=f03aef5a
-/
lemma addNullables_subset_generators {p : Finset g.NT} (hpg : p ⊆ g.generators) :
    addNullables p ⊆ g.generators := by
  unfold addNullables
  induction g.rules.toList.attach with
  | nil => simpa using hpg
  | cons a _ ih => exact addIfNullable_subset_generators ih (Finset.mem_toList.1 a.2)

/--
@isnad1 id=le.0h3v.s5.e4d83e55863d from=translated src=- shape=42a34e2a vocab=109a0b32
-/
lemma subset_addNullables (p : Finset g.NT) : p ⊆ (addNullables p) := by
  unfold addNullables
  induction g.rules.toList.attach with
  | nil => simp
  | cons a _ ih =>
    apply subset_trans ih
    apply subset_addIfNullable a.1

/--
@isnad1 id=lt.2h3v.s6.5dffb8e11e48 from=translated src=- shape=68717c49 vocab=2e5b7ca2
-/
lemma generators_limits_nullable {p : Finset g.NT}
    (hpg : p ⊆ g.generators) (hne : p ≠ addNullables p) :
    (g.generators).card - (addNullables p).card < (g.generators).card - p.card := by
  have hp := LE.le.ssubset_of_ne (subset_addNullables p) hne
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_lt_of_le
    · exact Finset.card_lt_card hp
    · exact Finset.card_le_card (addNullables_subset_generators hpg)
  · exact Finset.card_lt_card hp

/-- Fixpoint iteration computing the set of nullable symbols of `g`. -/
noncomputable def addNullablesIter (p : Finset g.NT) (hpg : p ⊆ g.generators) :=
  if p = addNullables p then
    p
  else
    addNullablesIter (addNullables p) (addNullables_subset_generators hpg)
  termination_by
    g.generators.card - p.card
  decreasing_by
    rename_i hp
    exact generators_limits_nullable hpg hp

/-- Compute the least-fixpoint of `add_nullable_iter`, i.e., all (and only) nullable symbols -/
noncomputable def computeNullables (g : ContextFreeGrammar T) [DecidableEq g.NT] :=
  addNullablesIter ∅ g.generators.empty_subset

/--
@isnad1 id=nullable.3h4v.s6.0bfb0505c8d7 from=translated src=- shape=2d3bc708 vocab=99034ae6
-/
lemma ruleIsNullable_NullableNonTerminal (p : Finset g.NT) (r : ContextFreeRule T g.NT)
    (hrg : r ∈ g.rules) (hn : ∀ v ∈ p, NullableNonTerminal v) (hr : ruleIsNullable p r) :
    NullableNonTerminal r.input := by
  unfold ruleIsNullable at hr
  unfold NullableNonTerminal
  have hrr : g.Produces [Symbol.nonterminal r.input] r.output := by
    use r, hrg
    rw [ContextFreeRule.rewrites_iff]
    use [], []
    simp
  apply Produces.trans_derives hrr
  apply symbols_nullable_nullableWord
  intro v hvr
  rw [decide_eq_true_eq] at hr
  specialize hr v hvr
  cases v <;> simp only [symbolIsNullable, decide_false, Bool.false_eq_true,
          decide_eq_true_eq] at hr
  exact hn _ hr

/--
@isnad1 id=nullable.2h4v.s6.a86c8628ea34 from=translated src=- shape=890290d6 vocab=63ee74cd
-/
lemma addNullables_mem_nullableNonTerminal (p : Finset g.NT) (hp : ∀ v ∈ p, NullableNonTerminal v) :
    ∀ v ∈ addNullables p, NullableNonTerminal v := by
  unfold addNullables
  induction g.rules.toList.attach with
  | nil => exact hp
  | cons a l ih =>
    simp only [List.foldr_cons, Finset.mem_toList, List.foldr_subtype, addIfNullable]
    split <;> rename_i hd
    · simp only [Finset.mem_insert, forall_eq_or_imp]
      constructor
      · apply ruleIsNullable_NullableNonTerminal _ _ (Finset.mem_toList.1 a.2) ih
        simpa [addIfNullable] using hd
      · simpa [addIfNullable] using ih
    · simpa [addIfNullable] using ih

/--
@isnad1 id=nullable.3h4v.s6.af4897014752 from=translated src=- shape=2be8cadb vocab=8dc5539e
-/
lemma addNullablesIter_only_nullableNonTerminal (p : Finset g.NT) (hpg : p ⊆ g.generators)
    (hp : ∀ v ∈ p, NullableNonTerminal v) :
    ∀ v ∈ (addNullablesIter p hpg), NullableNonTerminal v:= by
  unfold addNullablesIter
  intro
  split
  · tauto
  · exact addNullablesIter_only_nullableNonTerminal (addNullables p)
      (addNullables_subset_generators hpg) (addNullables_mem_nullableNonTerminal p hp) _
  termination_by ((g.generators).card - p.card)
  decreasing_by
    rename_i hp
    exact generators_limits_nullable hpg hp

/--
@isnad1 id=le.1h5v.s6.528c51a44c38 from=translated src=- shape=6c3e5565 vocab=bb0dff8a
-/
lemma addIfNullable_monotone {r : ContextFreeRule T g.NT} {p₁ p₂ : Finset g.NT} (hpp : p₁ ⊆ p₂) :
    addIfNullable r p₁ ⊆ addIfNullable r p₂ := by
  intro v hv
  unfold addIfNullable ruleIsNullable at hv ⊢
  by_cases hsr : decide (∀ s ∈ r.output, symbolIsNullable p₁ s) = true <;>
    simp only [hsr, reduceIte, Finset.mem_insert] at hv
  · split <;> rename_i hsr'
    · cases hv with
      | inl hvr =>
        simp_all
      | inr hv =>
        exact Finset.mem_insert_of_mem (hpp hv)
    · cases hv with
      | inl =>
        simp only [symbolIsNullable, decide_false, decide_eq_true_eq, not_forall,
          Bool.not_eq_true] at hsr' hsr
        obtain ⟨s, hsin, hs⟩ := hsr'
        specialize hsr s
        cases s with
        | terminal =>
          simp_all
        | nonterminal n =>
          rw [decide_eq_false_iff_not] at hs
          exfalso
          apply hs
          apply hpp
          simpa using hsr hsin
      | inr hvp₁ =>
        exact hpp hvp₁
  · split
    · exact Finset.mem_insert_of_mem (hpp hv)
    · exact hpp hv

private lemma subset_addIfNullable_rec {l : List (ContextFreeRule T g.NT)} {p : Finset g.NT} :
    p ⊆ List.foldr addIfNullable p l := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    apply Finset.Subset.trans ih
    apply subset_addIfNullable

/--
@isnad1 id=mem.2h4v.s6.bd99e1cae178 from=translated src=- shape=e83105fd vocab=984cf0bb
-/
lemma nullable_input_mem_addNullables {r : ContextFreeRule T g.NT} {p : Finset g.NT}
    (hpr : ruleIsNullable p r) (hrg : r ∈ g.rules) :
    r.input ∈ addNullables p := by
  unfold addNullables
  have hrg := List.mem_attach g.rules.toList ⟨r, (Finset.mem_toList.2 hrg)⟩
  revert r p
  induction g.rules.toList.attach with
  | nil =>
    simp
  | cons _ _ ih =>
    intro r' _ hr hr' hr''
    simp only [Finset.mem_toList, List.foldr_subtype, List.foldr_cons] at ih ⊢
    cases hr''
    · apply Finset.mem_of_subset (addIfNullable_monotone subset_addIfNullable_rec)
      simp [addIfNullable, hr]
    · rename_i hr''
      exact Finset.mem_of_subset (subset_addIfNullable _ _) (ih hr hr' hr'')

/--
@isnad1 id=eq.1h3v.s5.66f6e0bf0390 from=translated src=- shape=4918537a vocab=4bda2f2e
-/
lemma addNullablesIter_fixpoint {p : Finset g.NT} (hpg : p ⊆ g.generators) :
    addNullablesIter p hpg = addNullables (addNullablesIter p hpg) := by
  unfold addNullablesIter
  split
  · assumption
  · apply addNullablesIter_fixpoint
  termination_by ((g.generators).card - p.card)
  decreasing_by
    rename_i hp
    exact generators_limits_nullable hpg hp

/--
@isnad1 id=mem.2h5v.s6.fad58b0d3d92 from=translated src=- shape=61a230d8 vocab=8263e358
-/
lemma nullable_mem_addNullablesIter {p : Finset g.NT} (hpg : p ⊆ g.generators)
    (n : g.NT) (m : ℕ) (hvgm : g.DerivesIn [Symbol.nonterminal n] [] m) :
    n ∈ addNullablesIter p hpg := by
  cases m with
  | zero => cases hvgm
  | succ m =>
    obtain ⟨u, hwu, hue⟩ := hvgm.head_of_succ
    obtain ⟨r, hrg, hwu⟩ := hwu
    have hr : ruleIsNullable (addNullablesIter p hpg) r := by
      have hur : u = r.output := by
        obtain ⟨p, q, hv, hu⟩ := hwu.exists_parts
        cases p <;> simp at hv
        cases q <;> simp at hv
        simpa using hu
      unfold ruleIsNullable
      rw [decide_eq_true_eq]
      intro s hs
      rw [← hur] at hs
      obtain ⟨v', hv'⟩ := hue.nullable_mem_nonterminal hs
      unfold symbolIsNullable
      rw [hv', decide_eq_true_eq]
      have ⟨_, _, _⟩ := hue.mem_nullable hs
      apply nullable_mem_addNullablesIter
      rwa [← hv']
    have hv : n = r.input := by
      obtain ⟨p, q, hu, _⟩ := hwu.exists_parts
      cases p <;> simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq,
      Symbol.nonterminal.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at hu
      cases q <;> simp only [and_true, reduceCtorEq, and_false] at hu
      exact hu
    rw [addNullablesIter_fixpoint, hv]
    exact nullable_input_mem_addNullables hr hrg

/--
@isnad1 id=iff.0h3v.s5.eaff4386402f from=translated src=- shape=002d7188 vocab=e5545615
-/
lemma computeNullables_iff (n : g.NT) : n ∈ computeNullables g ↔ NullableNonTerminal n := by
  constructor
  · intro hng
    apply addNullablesIter_only_nullableNonTerminal _ _ _ _ hng
    tauto
  · intro hn
    obtain ⟨m, hgnm⟩ := (derives_iff_derivesIn _ _ _).1 hn
    apply nullable_mem_addNullablesIter
    exact hgnm

end ComputeNullables

/-! Definition and properties of `ContextFreeGrammar.eliminateEmpty`, the algorithm to remove all
rules with an empty right-hand side from a grammar. -/
section EliminateEmpty

variable {N : Type uN} [DecidableEq N]

/-- Compute all possible combinations of leaving out nullable nonterminals from `u` -/
def nullableCombinations (p : Finset N) (u : List (Symbol T N)) : List (List (Symbol T N)) :=
  match u with
  | [] => [[]]
  | x :: s =>
    match x with
    | Symbol.nonterminal n =>
      (if n ∈ p then nullableCombinations p s else []) ++
        (nullableCombinations p s).map (x :: ·)
    | Symbol.terminal _ => (nullableCombinations p s).map (x :: ·)

/-- Computes all variations of leaving out nullable symbols (except the empty string) of `r` -/
def removeNullableRule (p : Finset N) (r : ContextFreeRule T N) :=
  let fltrmap : List (Symbol T N) → Option (ContextFreeRule T N)
    | [] => Option.none
    | h :: t => Option.some ⟨r.input, h :: t⟩
  (nullableCombinations p r.output).filterMap fltrmap

variable {g : ContextFreeGrammar T}

/-- Compute all variations of leaving out nullable symbols (except empty string) of `g`s rules -/
noncomputable def removeNullables [DecidableEq T] [DecidableEq g.NT] (p : Finset g.NT) :=
  (g.rules.toList.map (removeNullableRule p)).flatten.toFinset

/-- Given `g`, computes a new grammar in which all rules deriving `[]` are removed and all rules
in `g` have a set of corresponding rules in g' in which some nullable symbols do not appear in
the output. For example if `r: V -> ABC` is in `g` and `A` and `B` are nullable, the rules
`r₁ : V -> ABC`, `r₂ : V -> BC`, `r₃ : V -> AC`, `r₄ : V -> C` will be in `g.eliminate_empty` -/
noncomputable def eliminateEmpty [DecidableEq T] (g : ContextFreeGrammar T)
    [DecidableEq g.NT] : ContextFreeGrammar T :=
  ⟨g.NT, g.initial, removeNullables g.computeNullables⟩

variable [DecidableEq g.NT]

/--
@isnad1 id=ne.1h5v.s6.4439b669c5cf from=translated src=- shape=e4e4bea9 vocab=e959a3d3
-/
lemma output_mem_removeNullableRule {r r' : ContextFreeRule T g.NT} {p : Finset g.NT}
    (hrr : r' ∈ removeNullableRule p r) :
    r'.output ≠ [] := by
  unfold removeNullableRule at hrr
  rw [List.mem_filterMap] at hrr
  obtain ⟨a, -, ha⟩ := hrr
  cases a <;> simp only [reduceCtorEq, Option.some.injEq] at ha
  rw [← ha]
  tauto

/--
@isnad1 id=ne.1h4v.s6.510f09d3a187 from=translated src=- shape=0612d026 vocab=0b919f97
-/
lemma output_mem_removeNullables [DecidableEq T] {r : ContextFreeRule T g.NT} {p : Finset g.NT}
    (hr : r ∈ removeNullables p) :
    r.output ≠ [] := by
  unfold removeNullables at hr
  rw [List.mem_toFinset, List.mem_flatten] at hr
  obtain ⟨l, hl, hr⟩ := hr
  rw [List.mem_map] at hl
  obtain ⟨r', _, hr'⟩ := hl
  rw [← hr'] at hr
  exact output_mem_removeNullableRule hr

/--
@isnad1 id=ne.1h4v.s5.2209f6d1ae16 from=translated src=- shape=436581de vocab=6b940ec9
-/
lemma eliminateEmpty_produces_not_empty [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : (g.eliminateEmpty).Produces u v) :
    v ≠ [] := by
  unfold Produces at huv
  change ∃ r ∈ (removeNullables g.computeNullables), r.Rewrites u v at huv
  obtain ⟨r, hrg, hr⟩ := huv
  intro hw
  rw [hw] at hr
  exact output_mem_removeNullables hrg hr.empty

/--
@isnad1 id=ne.2h4v.s6.9825fdf2aba1 from=translated src=- shape=f8be18fe vocab=a0a48277
-/
lemma eliminateEmpty_derives_not_empty [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : (g.eliminateEmpty).Derives u v) (hune : u ≠ []) :
    v ≠ [] := by
  change List (Symbol T g.eliminateEmpty.NT) at u v
  induction huv using Derives.head_induction_on with
  | refl => exact hune
  | head hp _ ih => exact ih (eliminateEmpty_produces_not_empty (g := g) hp)

/--
@isnad1 id=nullable.2h5v.s6.6cc46d08b048 from=translated src=- shape=511fa5b2 vocab=0b4e3c42
-/
lemma mem_nullableCombinations_nullableRelated {u v : List (Symbol T g.NT)} (p : Finset g.NT)
    (hn : ∀ x ∈ p, NullableNonTerminal x) (huv : u ∈ (nullableCombinations p v)) :
    NullableRelated u v := by
  induction v generalizing u with
  | nil =>
    simp only [nullableCombinations, List.mem_singleton] at huv
    rw [huv]
  | cons s v ih =>
    cases s with
    | nonterminal n =>
      simp only [nullableCombinations, List.mem_append, List.mem_ite_nil_right, List.mem_map] at huv
      cases huv with
      | inl hnu =>
        by_cases hnn : n ∈ p <;> simp only [hnn, false_and, true_and] at hnu
        exact NullableRelated.cons_nterm_nullable (ih hnu) (hn _ hnn)
      | inr huv =>
        obtain ⟨u', hu', rfl⟩ := huv
        exact NullableRelated.cons_nterm_match (ih hu') n
    | terminal t =>
      rw [nullableCombinations, List.mem_map] at huv
      obtain ⟨u', hu', rfl⟩ := huv
      exact NullableRelated.cons_term (ih hu') t

/--
@isnad1 id=and.1h4v.s6.0d4851a3e00d from=translated src=- shape=9b8bc109 vocab=732a3b97
-/
lemma mem_removeNullableRule_nullableRelated {r' : ContextFreeRule T g.NT}
    {r : ContextFreeRule T g.NT} {hrg : r ∈ removeNullableRule g.computeNullables r'} :
    r.input = r'.input ∧ NullableRelated r.output r'.output := by
  rw [removeNullableRule, List.mem_filterMap] at hrg
  obtain ⟨o, ho, ho'⟩ := hrg
  cases o <;> simp only [reduceCtorEq, Option.some.injEq] at ho'
  rw [← ho']
  constructor; · rfl
  apply mem_nullableCombinations_nullableRelated _ _ ho
  intro
  rw [computeNullables_iff]
  exact id

/--
@isnad1 id=ex.1h3v.s7.0035a11a0711 from=translated src=- shape=cee8bd36 vocab=ed9ff681
-/
lemma mem_eliminateEmpty [DecidableEq T] {r : ContextFreeRule T g.NT}
    (hrg : r ∈ g.eliminateEmpty.rules) :
    ∃ r' ∈ g.rules, r.input = r'.input ∧ NullableRelated r.output r'.output := by
  have hrg' : r ∈ (g.rules.toList.map (removeNullableRule g.computeNullables)).flatten :=
    List.mem_toFinset.1 hrg
  rw [List.mem_flatten] at hrg'
  obtain ⟨l, hl, hrl⟩ := hrg'
  obtain ⟨r', hgr', rfl⟩ := List.mem_map.1 hl
  exact ⟨r', Finset.mem_toList.1 hgr', mem_removeNullableRule_nullableRelated (hrg := hrl)⟩

/--
@isnad1 id=derives.1h4v.s5.37881944d436 from=translated src=- shape=88bf3049 vocab=da420a44
-/
lemma eliminateEmpty_produces_to_derives [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminateEmpty.Produces u v) :
    g.Derives u v := by
  obtain ⟨r, hrg, hr⟩ := huv
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  apply Derives.append_right
  apply Derives.append_left
  obtain ⟨r', hr', hrr', hnrr'⟩ := g.mem_eliminateEmpty hrg
  rw [hrr']
  exact (Produces.input_output hr').trans_derives hnrr'.derives

/--
@isnad1 id=derives.1h4v.s5.7e06220eeab5 from=translated src=- shape=8545ecec vocab=e6dd845d
-/
lemma eliminateEmpty_derives_to_derives [DecidableEq T] {u v : List (Symbol T g.NT)}
    (huv : g.eliminateEmpty.Derives u v) : g.Derives u v := by
  change (List (Symbol T g.eliminateEmpty.NT)) at u v
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact Derives.trans (eliminateEmpty_produces_to_derives hp) ih

/--
@isnad1 id=mem.0h4v.s5.3e13b7978a13 from=translated src=- shape=0ef2257d vocab=b6216fcf
-/
lemma mem_nullableCombinations (p : Finset g.NT) (u : List (Symbol T g.NT)) :
    u ∈ nullableCombinations p u := by
  induction u with
  | nil =>
    simp [nullableCombinations]
  | cons s _ ih =>
    cases s with
    | terminal t => simpa [nullableCombinations] using ih
    | nonterminal n => by_cases hn : n ∈ p <;> simp [nullableCombinations, hn, ih]

/--
@isnad1 id=mem.2h5v.s6.540b88740a89 from=translated src=- shape=786b3191 vocab=0b4e3c42
-/
lemma nullableRelated_mem_removeNullable {p : Finset g.NT} {u v : List (Symbol T g.NT)}
    (hvu : NullableRelated v u) (hn : ∀ s, s ∈ p ↔ NullableNonTerminal s) :
    v ∈ nullableCombinations p u := by
  induction u generalizing v with
  | nil =>
    rw [hvu.empty_right]
    exact List.mem_singleton.2 rfl
  | cons a l ih =>
    cases a with
    | terminal t =>
      rw [nullableCombinations, List.mem_map]
      cases hvu with
      | empty_left _ hvu => exact hvu.cons_terminal.elim
      | cons_term hu => exact ⟨_, ih hu, rfl⟩
    | nonterminal n =>
      rw [nullableCombinations, List.mem_append, List.mem_ite_nil_right, List.mem_map]
      cases hvu with
      | empty_left _ hu =>
        left
        rw [← List.singleton_append] at hu
        rw [hn]
        exact ⟨hu.empty_of_append_left, ih (NullableRelated.empty_left l hu.empty_of_append_right)⟩
      | cons_nterm_match hu'u => exact Or.inr ⟨_, ih hu'u, rfl⟩
      | cons_nterm_nullable hvu hnn =>
        simp_all

variable [DecidableEq T]

/--
@isnad1 id=mem.2h4v.s6.9e5990e07875 from=translated src=- shape=0570da33 vocab=93188714
-/
lemma not_empty_mem_removeNullables (p : Finset g.NT) (r : ContextFreeRule T g.NT)
    (hrg : r ∈ g.rules) (hne : r.output ≠ []) :
    r ∈ removeNullables p := by
  unfold removeNullables
  rw [List.mem_toFinset, List.mem_flatten]
  use (removeNullableRule p r)
  constructor
  · simp only [List.mem_map, Finset.mem_toList]
    use r
  · unfold removeNullableRule
    rw [List.mem_filterMap]
    use r.output, mem_nullableCombinations p r.output
    obtain ⟨_, rₒ⟩ := r
    cases rₒ <;> tauto

/--
@isnad1 id=mem.3h4v.s7.5f26f1bba376 from=translated src=- shape=9fc75bde vocab=b04bd99d
-/
lemma nullableRelated_mem_eliminateEmpty_rules {r : ContextFreeRule T g.NT}
   {u : List (Symbol T g.NT)} (hur : NullableRelated u r.output) (hrg : r ∈ g.rules)
   (hu : u ≠ []) :
   ⟨r.input, u⟩ ∈ g.eliminateEmpty.rules := by
  unfold eliminateEmpty removeNullables
  rw [List.mem_toFinset, List.mem_flatten]
  use removeNullableRule g.computeNullables r
  unfold removeNullableRule
  constructor
  · rw [List.mem_map]
    exact ⟨r, Finset.mem_toList.2 hrg, rfl⟩
  · rw [List.mem_filterMap]
    use u, nullableRelated_mem_removeNullable hur computeNullables_iff
    cases u <;> trivial

/--
@isnad1 id=ex.2h5v.s6.d240eb569e5d from=translated src=- shape=e56a19b0 vocab=fe3180a2
-/
lemma produces_nullableRelated_to_derives {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hwv : NullableRelated w v) :
    ∃ u', NullableRelated u' u ∧ g.eliminateEmpty.Derives u' w := by
  obtain ⟨r, hrg, hr⟩ := huv
  rw [r.rewrites_iff] at hr
  obtain ⟨p, q, hv, hw⟩ := hr
  rw [hw] at hwv
  obtain ⟨w₁, w₂, w₃, hw, hw₁, hw₂, hw₃⟩ := hwv.append_split_three
  cases w₂ with
  | nil =>
    refine ⟨w, ?_, by rfl⟩
    rw [hv, hw]
    apply nullable_related_append (nullable_related_append hw₁ _) hw₃
    exact NullableRelated.empty_left _
      ((Produces.input_output hrg).trans_derives hw₂.empty_nullableWord)
  | cons d l =>
    exact ⟨w₁ ++ [Symbol.nonterminal r.input] ++ w₃,
      hv ▸ nullable_related_append (nullable_related_append hw₁ (by rfl)) hw₃,
      hw ▸ Produces.single
        ⟨⟨r.input, d :: l⟩, nullableRelated_mem_eliminateEmpty_rules hw₂ hrg (l.cons_ne_nil d),
          ContextFreeRule.rewrites_of_exists_parts _ w₁ w₃⟩⟩

/--
@isnad1 id=ex.2h5v.s6.388473ea6a94 from=translated src=- shape=70766d01 vocab=06f5cba6
-/
lemma derivesIn_non_empty_to_nullableRelated_derives {u v : List (Symbol T g.NT)}
    (hv : v ≠ []) {m : ℕ} (huv : g.DerivesIn u v m) :
    ∃ u', NullableRelated u' u ∧ g.eliminateEmpty.Derives u' v := by
  cases m with
  | zero =>
    cases huv
    exact ⟨u, NullableRelated.refl u, Derives.refl (g := g.eliminateEmpty) u⟩
  | succ n =>
    obtain ⟨u'', huu'', hvn⟩ := huv.head_of_succ
    obtain ⟨u', hru'', huw'⟩ := derivesIn_non_empty_to_nullableRelated_derives hv hvn
    obtain ⟨v', hvv', hv'u'⟩ := produces_nullableRelated_to_derives huu'' hru''
    exact ⟨v', hvv', hv'u'.trans huw'⟩

/--
@isnad1 id=derives.2h5v.s6.291d599f2507 from=translated src=- shape=44853aef vocab=1bbe1fe1
-/
lemma derivesIn_to_eliminateEmpty_derives {w : List (Symbol T g.NT)} {n : g.NT} {hw : w ≠ []}
    {m : ℕ} (hnwm : g.DerivesIn [Symbol.nonterminal n] w m) :
    g.eliminateEmpty.Derives [Symbol.nonterminal n] w := by
  obtain ⟨w', hw, hww⟩ := derivesIn_non_empty_to_nullableRelated_derives hw hnwm
  cases hw with
  | empty_left =>
    obtain ⟨_, _⟩ := hww.eq_or_head
    · contradiction
    · apply Derives.of_empty at hww
      contradiction
  | cons_nterm_match hx _ =>
    cases hx
    exact hww
  | cons_nterm_nullable hxy hn =>
    rw [NullableRelated.empty_right hxy] at hww
    have := hww.of_empty
    contradiction

/--
@isnad1 id=eq.0h2v.s5.db94e8ae563e from=translated src=- shape=29de2fbd vocab=ba102fc0
-/
theorem eliminateEmpty_correct : g.language \ {[]} = g.eliminateEmpty.language := by
  apply Set.eq_of_subset_of_subset <;> intro w hw
  · have hw' : w ∈ g.language := hw.1
    have hw'' := hw.2
    rw [mem_language_iff, g.derives_iff_derivesIn] at hw'
    obtain ⟨n, hgwn⟩ := hw'
    refine derivesIn_to_eliminateEmpty_derives (hw := ?_) hgwn
    intro hw
    replace hw : w = [] := List.map_eq_nil_iff.1 hw
    rw [hw] at hw''
    exact hw'' rfl
  · replace hw : w ∈ g.eliminateEmpty.language := hw
    rw [mem_language_iff] at hw
    refine ⟨eliminateEmpty_derives_to_derives hw, fun hw' => ?_⟩
    replace hw' : w = [] := hw'
    apply eliminateEmpty_derives_not_empty hw
    · exact List.cons_ne_nil _ []
    · rw [hw']
      exact List.map_nil

end EliminateEmpty

end ContextFreeGrammar
