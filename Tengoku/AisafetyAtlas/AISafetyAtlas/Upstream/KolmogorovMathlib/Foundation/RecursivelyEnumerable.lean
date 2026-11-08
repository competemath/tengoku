/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.Seed.Computability.Partrec
public import Tengoku.Seed.Computability.PartrecCode
public import Tengoku.Seed.Computability.Primrec.List
public import Tengoku.Seed.Data.List.Basic
public import Tengoku.Seed.Data.Nat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Computably Enumerable Sets

This module establishes the abstract definitions of Computably Enumerable (RE) and co-RE sets,
along with their closure properties (like bounded existential search), and standard
utilities for generating bounded lists of booleans.
-/

namespace Kolmogorov

/-! ### Computably Enumerable (RE) Relations -/

/-- A relation is Computably Enumerable (RE) if it is the domain of a partial recursive function.-/
@[expose]
public def IsRE {α : Type*} [Primcodable α] (R : α → Prop) : Prop :=
  ∃ f : α →. Unit, Partrec f ∧ ∀ a, (f a).Dom ↔ R a

/-- A relation is co-RE if its complement is RE.-/
@[expose]
public def IsCoRE {α : Type*} [Primcodable α] (R : α → Prop) : Prop :=
  IsRE (fun a ↦ ¬ R a)

/-! ### Bounded Search and Dovetailing -/

/-- Auxiliary lemma: Establishes the equivalence between the domain of a partial
recursive function and the existence of a finite step count `k` for which the
evaluation of its code halts (`isSome = true`).-/
private lemma partrecCodeDom {α : Type*} [Primcodable α]
    (g : α →. Unit) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := α) n)).bind
        (fun a ↦ Part.map Encodable.encode (g a)))
    (a : α) :
    (g a).Dom ↔ ∃ k, (Nat.Partrec.Code.evaln k c (Encodable.encode a)).isSome := by
  have h_eval : (c.eval (Encodable.encode a)).Dom ↔ (g a).Dom := by aesop
  convert h_eval.symm using 1
  simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete]
  constructor
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c (Encodable.encode a) <;> aesop
  · rintro ⟨y, k, hk⟩
    exact ⟨k, by aesop⟩

/-- Helper 1: Computability of looking up the item in the list-/
private lemma dovetailLookupComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (bound : α → List β) (h_bound : Computable bound) :
    Computable (fun p : α × ℕ ↦ (bound p.1)[p.2.unpair.1]?) := by
  have h_fst : Computable (fun p : α × ℕ ↦ bound p.1) :=
    Computable.comp h_bound Computable.fst
  have h_idx : Computable (fun p : α × ℕ ↦ p.2.unpair.1) :=
    Computable.comp Computable.fst (Computable.comp Computable.unpair Computable.snd)
  exact Computable.comp Computable.list_getElem? (Computable.pair h_fst h_idx)

/-- Helper 2: Core computability of evaln with a fixed code-/
private lemma evalnCoreComputable (c : Nat.Partrec.Code) :
    Computable (fun p : ℕ × ℕ ↦ Nat.Partrec.Code.evaln p.1 c p.2) := by
  have h_prim : Primrec (fun p : ℕ × ℕ ↦ Nat.Partrec.Code.evaln p.1 c p.2) := by
    convert Nat.Partrec.Code.primrec_evaln using 1
    constructor <;> intro h
    · convert Nat.Partrec.Code.primrec_evaln using 1
    · convert h.comp (show Primrec (fun p : ℕ × ℕ ↦ ((p.1, c), p.2)) from ?_) using 1
      exact Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd
  exact Primrec.to_comp h_prim

/-- Helper 3: Computability of advancing the machine state-/
private lemma dovetailStepComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (c : Nat.Partrec.Code) :
    Computable₂ (fun (p : α × ℕ) (b : β) ↦
      Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b))) := by
  have h_steps : Computable (fun q : (α × ℕ) × β ↦ q.1.2.unpair.2 + 1) := by
    have hp : Primrec (fun q : (α × ℕ) × β ↦ q.1.2.unpair.2 + 1) :=
      Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
    exact Primrec.to_comp hp
  have h_input : Computable (fun q : (α × ℕ) × β ↦ Encodable.encode (q.1.1, q.2)) := by
    have hp : Primrec (fun q : (α × ℕ) × β ↦ (q.1.1, q.2)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
    exact Computable.comp Computable.encode (Primrec.to_comp hp)
  exact Computable.comp (evalnCoreComputable c) (Computable.pair h_steps h_input)

/-- The dovetailing check function is computable. It unpairs the index `n` into
a candidate index and step count, retrieves the candidate, and runs the evaluation.-/
private lemma dovetailCheckComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (bound : α → List β) (h_bound : Computable bound) (c : Nat.Partrec.Code) :
    Computable₂ (fun (a : α) (n : ℕ) ↦
      match (bound a)[n.unpair.1]? with
      | some b =>
        (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      | none => false) := by
  have h_lookup := dovetailLookupComputable bound h_bound
  have h_step := dovetailStepComputable (α := α) (β := β) c
  have h_bind := Computable.option_bind h_lookup h_step
  have h_isSome : Computable (fun o : Option ℕ ↦ o.isSome) :=
    Primrec.to_comp Primrec.option_isSome
  have h_full : Computable (fun p : α × ℕ ↦
      ((bound p.1)[p.2.unpair.1]?.bind (fun b ↦
        Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b)))).isSome) :=
    Computable.comp h_isSome h_bind
  exact Computable.of_eq h_full (by
    intro p
    dsimp only
    cases h : (bound p.1)[p.2.unpair.1]? <;> rfl)

/-! ### Bounded Generators (For Bitstrings) -/

/-- Generates all bitstrings (lists of booleans) of exactly length n.-/
@[expose]
public def exactLengthPrograms : ℕ → List (List Bool)
  | 0 => [[]]
  | (n + 1) => (exactLengthPrograms n).flatMap fun s ↦ [false :: s, true :: s]

/-- Generates all bitstrings of length ≤ N.-/
@[expose]
public def boundedPrograms (N : ℕ) : List (List Bool) :=
  (List.range (N + 1)).flatMap exactLengthPrograms

/-- Helper: programs generated by `exactLengthPrograms n` have length `n`.-/
private lemma exactLengthPrograms_length (n : ℕ) (p : List Bool) :
    p ∈ exactLengthPrograms n → p.length = n := by
  induction n generalizing p with
  | zero =>
    intro h
    have : p = [] := by simpa [exactLengthPrograms] using h
    rw [this]
    rfl
  | succ n ih =>
    intro h
    have : ∃ s ∈ exactLengthPrograms n, p = false :: s ∨ p = true :: s := by
      simpa [exactLengthPrograms] using h
    rcases this with ⟨s, hs_mem, rfl | rfl⟩
    · simp [ih s hs_mem]
    · simp [ih s hs_mem]

/-- Helper: any list belongs to `exactLengthPrograms` of its own length.-/
private lemma mem_exactLengthPrograms_self (p : List Bool) :
    p ∈ exactLengthPrograms p.length := by
  induction p with
  | nil => simp [exactLengthPrograms]
  | cons b tail ih =>
    simp only [exactLengthPrograms, List.length_cons, List.mem_flatMap]
    refine ⟨tail, ih, ?_⟩
    cases b <;> simp

/-
`exactLengthPrograms n` has no duplicates.
-/

/-
`boundedPrograms N` has no duplicates.
-/
-- Closes the indexed disjointness goal after extracting exact lengths from both
-- sides, via a squeezed `simp_all only` over the range-index rewrites.

end Kolmogorov
