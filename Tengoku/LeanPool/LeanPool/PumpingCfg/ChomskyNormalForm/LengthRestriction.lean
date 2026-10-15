/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/
module

public import Tengoku.LeanPool.LeanPool.PumpingCfg.ChomskyNormalForm.Basic
import Tengoku.LeanPool.LeanPool.PumpingCfg.ChomskyNormalForm.ContextFreeGrammarExtras

/-!
# Length Restriction

This file contains the algorithm to translate a `ContextFreeGrammar.Wellformed` grammar to a
chomsky normal form grammar while preserving the language of the original grammar. A context-free
grammar is wellformed if it has rules that rewrite either to a single terminal or multiple
nonterminals.

## Main definitions
* `ContextFreeGrammar.restrictLength`: Transforms a context-free grammar to a chomsky normal form
grammar by replacing rules that rewrite to multiple nonterminals to a set of cascading rules.

## Main theorems
* `ContextFreeGrammar.restrictLength_correct`: The transformed grammar's language coincides with
the original

## References
* [John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman. 2006. Introduction to Automata Theory,
   Languages, and Computation (3rd Edition). Addison-Wesley Longman Publishing Co., Inc., USA.]
   [Hopcroft et al. 2006]
-/

@[expose] public section

universe uN uT
variable {T : Type uT}

namespace ContextFreeRule
variable {N : Type*}

/-- `Wellformed r` holds if the rule's output is not a single nonterminal (`UnitRule`), not empty,
 or if the output is more than one symbol, it is only nonterminals -/
inductive Wellformed : (ContextFreeRule T N) → Prop where
  /-- Rule rewriting to a single terminal is wellformed -/
  | terminal {n : N} (t : T) : Wellformed ⟨n, [Symbol.terminal t]⟩
  /-- Rule rewriting to mulitple nonterminals is wellformed -/
  | nonterminals {n : N} (u : List (Symbol T N)) (h2 : 2 ≤ u.length)
      (hu : ∀ s ∈ u, match s with | Symbol.nonterminal _ => True | _ => False) :
      Wellformed ⟨n, u⟩

/--
@isnad1 id=ex.0h4v.s6.a7fbfb248c8e from=translated src=- shape=9a0506e9 vocab=1b14f672
-/
lemma only_nonterminals {u : List (Symbol T N)}
    (hu : ∀ s ∈ u, match s with | Symbol.nonterminal _ => True | _ => False) :
    ∃ v : List N, v.map Symbol.nonterminal = u := by
  induction u with
  | nil => use []; rfl
  | cons a _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hu
    obtain ⟨u', hu'⟩ := ih hu.2
    cases a
    · simp at hu
    · rename_i n
      use n :: u'
      simpa only [List.map_cons, List.cons.injEq, true_and] using hu'

/--
@isnad1 id=ex.2h4v.s7.18da7b171808 from=translated src=- shape=aa621262 vocab=5b5d4e89
-/
lemma Wellformed.mem_nonterminal {r : ContextFreeRule T N} (hr : r.Wellformed)
    (i : Fin r.output.length) (h2 : 2 ≤ r.output.length) :
    ∃ n, r.output[i] = Symbol.nonterminal n := by
  induction hr with
  | terminal => simp at h2
  | nonterminals u _ hu =>
    simp only [Fin.getElem_fin] at i ⊢
    specialize hu (u[i]'i.2) (u.get_mem i)
    aesop

/--
@isnad1 id=or.1h3v.s6.152c767427d2 from=translated src=- shape=f0ae8717 vocab=1e588f0d
-/
lemma Wellformed.cases {r : ContextFreeRule T N} (hr : r.Wellformed) :
    (∃ t : T, r.output = [Symbol.terminal t]) ∨
    (∃ (n₁ n₂ : N) (u : List N),
      r.output = Symbol.nonterminal n₁ :: Symbol.nonterminal n₂ :: u.map Symbol.nonterminal) := by
  induction hr with
  | terminal t => left; use t
  | nonterminals u _ hu =>
    match u with
    | [] => contradiction
    | [_] => contradiction
    | .terminal t :: _ :: _ => specialize hu (Symbol.terminal t); simp at hu
    | _ :: .terminal t :: _ => specialize hu (Symbol.terminal t); simp at hu
    | .nonterminal n₁ :: .nonterminal n₂ :: u =>
      right
      simp only [List.mem_cons, forall_eq_or_imp, true_and] at hu
      obtain ⟨u', huu⟩ := only_nonterminals hu
      use n₁, n₂, u'
      simp [huu.symm]

end ContextFreeRule

namespace ContextFreeGrammar

/-! Definition of `ContextFreeGrammar.restrictLength`, the algorithm to translate a wellformed
context-free grammar to a chomsky normal form grammar -/
section RestrictLength

variable {g : ContextFreeGrammar T}

/-- Shorthand for the new type of nonterminals. -/
abbrev NT' := g.NT ⊕ Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)

/-- Computes a cascade of rules generating `r.output` if it only contains nonterminals. For a rule
 r : n -> n₁n₂n₃n₄, generates rules n -> n₁m₂, m₂ -> n₂m₃, and m₃ -> n₃n₄. The type of of NT',
 encodes the correspondence between rules and the new nonterminals. -/
def computeRulesRec (r : ContextFreeRule T g.NT) (i : Fin (r.output.length - 2)) :
    List (ChomskyNormalFormRule T g.NT') :=
  match i with
  | ⟨0, p⟩ => match r.output.get ⟨r.output.length - 2, by omega⟩,
                r.output.get ⟨r.output.length - 1, by omega⟩ with
             | Symbol.nonterminal n₁, Symbol.nonterminal n₂ =>
               [(ChomskyNormalFormRule.node (Sum.inr ⟨r, ⟨0, p⟩⟩) (Sum.inl n₁) (Sum.inl n₂))]
             | _, _ => []
  | ⟨n + 1, p⟩ => match r.output.get ⟨r.output.length - 2 - i.val, by omega⟩ with
                 | Symbol.nonterminal n' =>
                   (ChomskyNormalFormRule.node (Sum.inr ⟨r, ⟨i.val, by omega⟩⟩) (Sum.inl n')
                     (Sum.inr ⟨r, ⟨n, by omega⟩⟩))
                   :: computeRulesRec r ⟨n, by omega⟩
                 | _ => []

/-- We assume all rules' output is either a pair of nonterminals, a single terminal or a string of
 at least 3 nonterminals. In the first two cases we can directly translate them, otherwise we
 generate new rules using `compute_rules_rec`. -/
def computeRules (r : ContextFreeRule T g.NT) : List (ChomskyNormalFormRule T g.NT') :=
  match hr : r.output with
  | [Symbol.nonterminal n₁, Symbol.nonterminal n₂] =>
      [ChomskyNormalFormRule.node (Sum.inl r.input) (Sum.inl n₁) (Sum.inl n₂)]
  | [Symbol.terminal t] =>
      [ChomskyNormalFormRule.leaf (Sum.inl r.input) t]
  | Symbol.nonterminal n :: _ :: _ :: _ =>
      ChomskyNormalFormRule.node (Sum.inl r.input) (Sum.inl n)
        (Sum.inr ⟨r, ⟨r.output.length - 3, by simp [hr]⟩⟩)
      :: computeRulesRec r ⟨r.output.length - 3, by simp [hr]⟩
  | _ => []

/-- Compute all `ChomskyNormalFormRule`s corresponding to the original `ContextFreeRule`s -/
def restrictLengthRules [DecidableEq T] [DecidableEq g.NT] (l : List (ContextFreeRule T g.NT)) :=
  (l.map computeRules).flatten.toFinset

end RestrictLength

/-- Construct a `ChomskyNormalGrammar` corresponding to the original `ContextFreeGrammar` -/
noncomputable def restrictLength [DecidableEq T] (g : ContextFreeGrammar T)
    [e : DecidableEq g.NT] :=
  ChomskyNormalFormGrammar.mk g.NT' (Sum.inl g.initial) (restrictLengthRules g.rules.toList)

/-- A grammar is `Wellformed` if all rules are `ContextFreeRule.Wellformed` -/
def Wellformed (g : ContextFreeGrammar T) : Prop := ∀ r ∈ g.rules, r.Wellformed

/-! Definitions of embeding into and projecting to the type of symbols of the new grammar -/
section EmbedProject

variable {g : ContextFreeGrammar T}

/-- Intuitive embedding of symbols of the original grammar into symbols of the new grammar's type -/
def embedSymbol (s : Symbol T g.NT) : Symbol T g.NT' :=
  match s with
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl n)

/--
@isnad1 id=eq.0h3v.s6.a74ef64bbc9f from=translated src=- shape=9b5bb8c7 vocab=b9471116
-/
lemma embedSymbol_nonterminal {n : g.NT} :
    embedSymbol (Symbol.nonterminal n) = Symbol.nonterminal (Sum.inl n) := by rfl

/--
@isnad1 id=eq.0h3v.s4.4d3eb194effc from=translated src=- shape=d42075e8 vocab=2676b4b7
-/
lemma embedSymbol_terminal {t : T} :
    embedSymbol (Symbol.terminal t) = (@Symbol.terminal T g.NT') t := by rfl

/-- Intuitive embedding of strings of the original grammar into strings of the new grammar's type -/
abbrev embedString (u : List (Symbol T g.NT)) : List (Symbol T g.NT') := u.map embedSymbol

/--
@isnad1 id=eq.0h3v.s7.4a166528f5a6 from=translated src=- shape=52e555ac vocab=b4a21f67
-/
lemma embedString_nonterminal {n : g.NT} :
    embedString [Symbol.nonterminal n] = [Symbol.nonterminal (Sum.inl n)] := rfl

/--
@isnad1 id=eq.0h3v.s5.66395884aa90 from=translated src=- shape=b3c7342e vocab=29913aa9
-/
lemma embedString_terminals {u : List T} :
    embedString (u.map Symbol.terminal) = u.map (@Symbol.terminal T g.NT') := by
  induction u with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_map, List.map_inj_left, Function.comp_apply, List.map_cons, List.cons.injEq]
      at ih ⊢
    exact ⟨rfl, ih⟩

/--
@isnad1 id=eq.0h4v.s6.25712132666d from=translated src=- shape=7a4358b3 vocab=b0c281fe
-/
lemma embedString_append {u v : List (Symbol T g.NT)} :
  embedString (u ++ v) = embedString u ++ embedString v := List.map_append

/-- Projection from symbols of the new grammars type into symbols of the original grammar -/
def projectSymbol (s : Symbol T g.NT') : List (Symbol T g.NT) :=
  match s with
  | Symbol.terminal t => [Symbol.terminal t]
  | Symbol.nonterminal (Sum.inl n) => [Symbol.nonterminal n]
  | Symbol.nonterminal (Sum.inr ⟨r, ⟨i, _⟩⟩) => List.drop (r.output.length - 2 - i) r.output

/-- Projection from strings of the new grammars type into strings of the original grammar -/
abbrev projectString (u : List (Symbol T g.NT')) : List (Symbol T g.NT) :=
  (u.map projectSymbol).flatten

/--
@isnad1 id=eq.0h4v.s6.aeba1bcc91de from=translated src=- shape=7a4358b3 vocab=6329218c
-/
lemma projectString_append {u v : List (Symbol T g.NT')} :
    projectString (u ++ v) = projectString u ++ projectString v := by
  unfold projectString
  rw [List.map_append, List.flatten_append]

/--
@isnad1 id=eq.0h3v.s4.f5a03ecd9010 from=translated src=- shape=19c1bdeb vocab=a908344a
-/
lemma projectString_embedString_id {u : List (Symbol T g.NT)} :
    projectString (embedString u) = u := by
  unfold projectString embedString
  induction u with
  | nil => rfl
  | cons d _ ih =>
    simp only [List.map_map, List.map_cons, List.flatten_cons] at ih ⊢
    rw [← List.singleton_append, ih]
    congr
    cases d <;> rfl

/--
@isnad1 id=eq.0h3v.s6.7a38744bbe3f from=translated src=- shape=8499be80 vocab=9ef6e09f
-/
lemma projectString_nonterminal {n : g.NT} :
    projectString [Symbol.nonterminal (Sum.inl n)] = [Symbol.nonterminal n] := by
  simp [projectString, projectSymbol]

/--
@isnad1 id=eq.0h3v.s5.7da759d6a6bf from=translated src=- shape=884fb3a5 vocab=c6e03475
-/
@[simp]
lemma projectSymbol_terminal {t : T} :
    projectSymbol (@Symbol.terminal T g.NT' t) = [Symbol.terminal t] := by
  simp [projectSymbol]

/--
@isnad1 id=eq.0h3v.s5.b389a0f18611 from=translated src=- shape=b3c7342e vocab=3538adb3
-/
lemma projectString_terminals {u : List T} :
    projectString (u.map (@Symbol.terminal T g.NT')) = u.map Symbol.terminal := by
  induction u with
  | nil => rfl
  | cons =>
    rw [← List.singleton_append, List.map_append, List.map_append, projectString_append]
    congr

end EmbedProject

variable {g : ContextFreeGrammar T}

/--
@isnad1 id=eq.1h5v.s6.fc715ebd1006 from=translated src=- shape=8a72242a vocab=a912ddd5
-/
lemma mem_computeRulesRec_projectString_input_eq_output {r : ContextFreeRule T g.NT}
    {i : Fin (r.output.length - 2)} {r' : ChomskyNormalFormRule T g.NT'}
    (hrri : r' ∈ computeRulesRec r i) :
    projectString r'.output = projectString [Symbol.nonterminal r'.input] := by
  obtain ⟨m, _⟩ := i
  induction m with
  | zero =>
    simp only [computeRulesRec, List.get_eq_getElem] at hrri
    split at hrri <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hrri
    · rename_i n₁ n₂ hn₁ hn₂
      rw [hrri, ChomskyNormalFormRule.input, ChomskyNormalFormRule.output]
      simp only [projectString, projectSymbol, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.singleton_append, Nat.sub_zero, List.append_nil]
      rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
      swap; · omega
      swap; · omega
      congr
      · rw [← hn₁]
      · rw [← hn₂]
        congr
        omega
      · rw [List.nil_eq, List.drop_eq_nil_iff]
        omega
  | succ _ ih =>
    simp only [computeRulesRec, List.get_eq_getElem] at hrri
    split at hrri <;>
      simp only [Nat.succ_eq_add_one, List.mem_cons, List.not_mem_nil] at hrri
    cases hrri <;> rename_i heq hrri
    · rw [hrri]
      simp only [ChomskyNormalFormRule.input, ChomskyNormalFormRule.output, projectString,
        projectSymbol, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.singleton_append]
      nth_rewrite 2 [List.drop_eq_getElem_cons]
      · congr
        · exact heq.symm
        · omega
    · exact ih _ hrri

/--
@isnad1 id=not.1h6v.s6.2f876233ff50 from=translated src=- shape=ac4c2f5a vocab=ee4cfe70
-/
lemma left_not_mem_computeRulesRec {n : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ChomskyNormalFormRule T g.NT'} {i : Fin (r.output.length - 2)}
    (hrn : r'.input = Sum.inl n) :
    r' ∉ computeRulesRec r i := by
  obtain ⟨m, _⟩ := i
  induction m with
  | zero =>
    unfold computeRulesRec
    split
    · simp only [List.mem_singleton]
      intro hr'
      simp_all
    · exact List.not_mem_nil
  | succ _ ih =>
    unfold computeRulesRec
    split
    · simp only [List.mem_cons, not_or]
      constructor
      · intro h
        simp_all
      · apply ih
    · exact List.not_mem_nil

/--
@isnad1 id=le.2h5v.s7.d1231a710291 from=translated src=- shape=f04fc7d1 vocab=f117be4b
-/
lemma mem_computRules_right_length {n : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)}
    {r : ContextFreeRule T g.NT} {r' : ChomskyNormalFormRule T g.NT'} (hrr : r' ∈ computeRules r)
    (hrn : r'.input = Sum.inr n) :
    3 ≤ r.output.length := by
  unfold computeRules at hrr
  split at hrr <;> try rw [List.mem_singleton] at hrr
  · rw [hrr] at hrn; simp at hrn
  · rw [hrr] at hrn; simp at hrn
  · rename_i heq; simp [heq]
  · contradiction

/--
@isnad1 id=mem.3h5v.s8.d8fef070d62e from=translated src=- shape=d8f7e6f9 vocab=00db930d
-/
lemma mem_computeRules_right_mem_computeRulesRec
    {n : Σ r : ContextFreeRule T g.NT, Fin (r.output.length - 2)} {r : ContextFreeRule T g.NT}
    {r' : ChomskyNormalFormRule T g.NT'} (hrₒ : r.output.length - 3 < r.output.length - 2)
    (hrr : r' ∈ computeRules r) (hrn : r'.input = Sum.inr n) :
    r' ∈ computeRulesRec r ⟨r.output.length - 3, hrₒ⟩ := by
  unfold computeRules at hrr
  split at hrr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hrr
  · rw [hrr] at hrn; simp at hrn
  · rw [hrr] at hrn; simp at hrn
  · cases hrr <;> rename_i hrr
    · rw [hrr] at hrn; simp at hrn
    · exact hrr

/--
@isnad1 id=and.2h5v.s7.f7af53b5baf0 from=translated src=- shape=3c31780a vocab=51e3d210
-/
lemma mem_computeRules_left {n : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ChomskyNormalFormRule T g.NT'}
    (hrr : r' ∈ computeRules r) (hrn : r'.input = Sum.inl n) :
    projectString r'.output = r.output ∧ n = r.input := by
  unfold computeRules at hrr
  split at hrr
  · rename_i n₁ n₂ hrnn
    rw [List.mem_singleton] at hrr
    rw [hrr, hrnn]
    rw [hrr] at hrn
    simp only [projectString, projectSymbol, ChomskyNormalFormRule.input, Sum.inl.injEq,
      ChomskyNormalFormRule.output, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.singleton_append, true_and] at hrn ⊢
    exact hrn.symm
  · rename_i t heq2
    rw [List.mem_singleton] at hrr
    rw [hrr, heq2]
    rw [hrr] at hrn
    simp only [projectString, projectSymbol, ChomskyNormalFormRule.input, Sum.inl.injEq,
      ChomskyNormalFormRule.output, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.singleton_append, true_and] at hrn ⊢
    exact hrn.symm
  · rw [List.mem_cons] at hrr
    cases hrr <;> rename_i heq2 hrr
    · constructor
      · rw [hrr]
        simp only [ChomskyNormalFormRule.output]
        rw [← List.singleton_append, projectString_append]
        simp only [projectString, projectSymbol, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.singleton_append, List.append_nil]
        simp_all
      · simp_all
    · exfalso
      exact left_not_mem_computeRulesRec hrn hrr
  · contradiction

/--
@isnad1 id=derives.1h4v.s5.9d5997893097 from=translated src=- shape=e68068c7 vocab=7b373604
-/
lemma restrictLength_produces_derives_projectString {u v : List (Symbol T g.NT')} [DecidableEq T]
    [DecidableEq g.NT] (huv : g.restrictLength.Produces u v) :
    g.Derives (projectString u) (projectString v) := by
  have huv' : ∃ r ∈ restrictLengthRules g.rules.toList, r.Rewrites u v := huv
  obtain ⟨r, hrg, huv⟩ := huv'
  obtain ⟨p, q, hu, hv⟩ := huv.exists_parts
  rw [hu, hv]
  repeat rw [projectString_append]
  apply Derives.append_right
  apply Derives.append_left
  simp only [restrictLengthRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨r', hrg', hrr⟩ := hrg
  cases hr : r.input with
  | inl =>
    obtain ⟨heqo, heqi⟩ := mem_computeRules_left hrr hr
    rw [heqo, heqi, projectString]
    exact (Produces.input_output hrg').single
  | inr =>
    rw [mem_computeRulesRec_projectString_input_eq_output, hr]
    exact mem_computeRules_right_mem_computeRulesRec
      (Nat.sub_lt_sub_left (mem_computRules_right_length hrr hr) (Nat.lt_add_one 2)) hrr hr

/--
@isnad1 id=derives.1h4v.s5.2a25f97c196e from=translated src=- shape=e68068c7 vocab=dd501cdc
-/
lemma restrictLength_derives_derives_projectString {u v : List (Symbol T g.NT')} [DecidableEq T]
    [DecidableEq g.NT] (huv : g.restrictLength.Derives u v) :
    g.Derives (projectString u) (projectString v) := by
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact Derives.trans (restrictLength_produces_derives_projectString hp) ih

/--
@isnad1 id=derives.2h6v.s10.39b193697497 from=translated src=- shape=2d0fa88b vocab=272bece7
-/
lemma computeRulesRec_derives [DecidableEq T] [DecidableEq g.NT] {r : ContextFreeRule T g.NT}
    {i : Fin (r.output.length - 2)} {n : g.NT'} {x : List (ChomskyNormalFormRule T g.NT')}
    (hrix : computeRulesRec r i ⊆ x) (hr : r.Wellformed) :
    (ChomskyNormalFormGrammar.mk g.NT' n x.toFinset).Derives
      [Symbol.nonterminal (Sum.inr ⟨r, i⟩)]
      (embedString (List.drop (r.output.length - 2 - i) r.output)) := by
  obtain ⟨n, p⟩ := i
  induction n with
  | zero =>
    unfold computeRulesRec at hrix
    simp only [List.get_eq_getElem, Nat.sub_zero, List.map_drop] at hrix ⊢
    split at hrix
    · rename_i n₁ n₂ hrn₁ hrn₂
      have heq :
          (r.output.map embedSymbol).drop (r.output.length - 2) =
          embedString [Symbol.nonterminal n₁, Symbol.nonterminal n₂] := by
        have hrₒ : r.output.length - 2 + 1 + 1 = r.output.length := by omega
        rw [← List.map_drop, ← List.getElem_cons_drop,
          ← List.getElem_cons_drop]
        · rw [hrₒ, List.drop_length, hrn₁]
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
          congr
          rw [← hrn₂]
          congr
          omega
        all_goals omega
      rw [heq]
      simp only [List.map_cons, List.map_nil]
      rw [embedSymbol_nonterminal, embedSymbol_nonterminal]
      apply ChomskyNormalFormGrammar.Produces.single
      constructor
      · constructor
        · simp only [List.cons_subset, List.nil_subset, and_true, List.mem_toFinset] at hrix ⊢
          exact hrix
        · exact ChomskyNormalFormRule.Rewrites.input_output
    · rename_i hn
      exfalso
      obtain ⟨n₁, hn₁⟩ := hr.mem_nonterminal ⟨r.output.length - 2, by omega⟩ (by omega)
      obtain ⟨n₂, hn₂⟩ := hr.mem_nonterminal ⟨r.output.length - 1, by omega⟩ (by omega)
      exact hn _ _ hn₁ hn₂
  | succ n ih =>
    unfold computeRulesRec at hrix
    split at hrix
    · rename_i _ hrn
      simp only [List.cons_subset, List.get_eq_getElem] at hrix hrn
      obtain ⟨hx₁, hx₂⟩ := hrix
      rw [← List.getElem_cons_drop, hrn]
      · apply ChomskyNormalFormGrammar.Produces.trans_derives
        · constructor
          · constructor
            · simp only [List.mem_toFinset]
              exact hx₁
            · exact ChomskyNormalFormRule.Rewrites.input_output
        · simp only [ChomskyNormalFormRule.output, List.map_cons, List.map_drop]
          rw [← List.singleton_append, ← List.singleton_append, embedSymbol_nonterminal,
            ← List.map_drop]
          apply ChomskyNormalFormGrammar.Derives.append_left
          have hrₒ : r.output.length - 2 - (n + 1) + 1 = r.output.length - 2 - n := by omega
          simp_all
      · omega
    · rename_i hn
      obtain ⟨n₁, hn₁⟩ := hr.mem_nonterminal ⟨r.output.length - 2 - (n + 1), by omega⟩ (by omega)
      simp_all

/--
@isnad1 id=derives.2h5v.s10.bd5ebeb0bd06 from=translated src=- shape=c8d6ad2c vocab=22fae9d1
-/
lemma computeRules_derives_embedString [DecidableEq T] [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} {n : g.NT'} {x : List (ChomskyNormalFormRule T g.NT')}
    (hrx : computeRules r ⊆ x) (hr : r.Wellformed) :
    (ChomskyNormalFormGrammar.mk g.NT' n x.toFinset).Derives
      [Symbol.nonterminal (Sum.inl r.input)]
      (embedString r.output) := by
  unfold computeRules at hrx
  split at hrx <;> rename_i hrn
  · rename_i n₁ n₂
    simp only [List.cons_subset, List.nil_subset, and_true] at hrx
    apply ChomskyNormalFormGrammar.Produces.single
    constructor
    · constructor
      · rwa [List.mem_toFinset]
      · rw [hrn, embedString, List.map_cons, List.map_cons, List.map_nil,
          embedSymbol_nonterminal, embedSymbol_nonterminal]
        exact ChomskyNormalFormRule.Rewrites.input_output
  · rename_i t
    simp only [List.cons_subset, List.nil_subset, and_true] at hrx
    apply ChomskyNormalFormGrammar.Produces.single
    constructor
    · constructor
      · rwa [List.mem_toFinset]
      · rw [hrn, embedString, List.map_cons, List.map_nil, embedSymbol_terminal]
        exact ChomskyNormalFormRule.Rewrites.input_output
  · rename_i n' s₁ s₂ u
    rw [List.cons_subset] at hrx
    obtain ⟨hx₁, hx₂⟩ := hrx
    apply ChomskyNormalFormGrammar.Produces.trans_derives
    · constructor
      · constructor
        · rwa [List.mem_toFinset]
        · exact ChomskyNormalFormRule.Rewrites.input_output
    · nth_rewrite 4 [hrn]
      simp only [ChomskyNormalFormRule.output, List.map_cons]
      rw [← List.singleton_append, ← (@List.singleton_append _ (embedSymbol _)),
           embedSymbol_nonterminal]
      apply ChomskyNormalFormGrammar.Derives.append_left
      have heq :
        (embedSymbol s₁ :: embedSymbol s₂ :: u.map embedSymbol =
          embedString (List.drop (r.output.length - 2 - (r.output.length - 3)) r.output)) := by
        simp_all
      rw [heq]
      exact computeRulesRec_derives hx₂ hr
  · rename_i hrn' ht
    exfalso
    obtain (⟨t, heq⟩ | ⟨n₁, n₂, u, hru⟩) := hr.cases
    · exact ht t heq
    · cases u
      · exact hrn' n₁ n₂ hru
      · exact hrn _ _ _ _ hru

/--
@isnad1 id=derives.2h4v.s5.0a091b1bb665 from=translated src=- shape=d49c7665 vocab=f3f26641
-/
lemma produces_restrictLength_derives_embedString [DecidableEq T] [DecidableEq g.NT]
    {u v : List (Symbol T g.NT)} (huv : g.Produces u v) (hg : g.Wellformed) :
    g.restrictLength.Derives (embedString u) (embedString v) := by
  obtain ⟨r, hrg, hr⟩ := huv
  obtain ⟨_, _, hu, hv⟩ := hr.exists_parts
  rw [hu, hv]
  repeat rw [embedString_append]
  apply ChomskyNormalFormGrammar.Derives.append_right
  apply ChomskyNormalFormGrammar.Derives.append_left
  rw [embedString_nonterminal]
  apply computeRules_derives_embedString _ (hg _ hrg)
  intro r' _
  simp only [List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and]
  use r

/--
@isnad1 id=derives.2h4v.s5.56430596b4e2 from=translated src=- shape=d49c7665 vocab=9b73ad80
-/
lemma derives_restrictLength_derives_embedString [DecidableEq T] [DecidableEq g.NT]
    {u v : List (Symbol T g.NT)} (huv : g.Derives u v) (hg : g.Wellformed) :
    g.restrictLength.Derives (embedString u) (embedString v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact (produces_restrictLength_derives_embedString hp hg).trans ih

/--
@isnad1 id=eq.1h2v.s4.919fc30eb4dd from=translated src=- shape=76b967f0 vocab=66c0d807
-/
theorem restrictLength_correct [DecidableEq T] [e : DecidableEq g.NT] (hg : g.Wellformed) :
    g.language = g.restrictLength.language := by
  apply Set.eq_of_subset_of_subset <;> intro w hw
  · apply derives_restrictLength_derives_embedString at hw
    rw [embedString_nonterminal, embedString_terminals] at hw
    exact hw hg
  · apply restrictLength_derives_derives_projectString at hw
    simp only [restrictLength] at hw
    rw [projectString_nonterminal, projectString_terminals] at hw
    exact hw

end ContextFreeGrammar
