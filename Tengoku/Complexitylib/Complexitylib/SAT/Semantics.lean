/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# SAT: Semantic Layer

This file contains the mathematical definition of Boolean satisfiability.
**No Turing machines are used here.** Everything is pure recursion on
inductive types; a reader can audit these definitions in a few minutes
and check that they really capture "α satisfies φ".

All later claims about the SAT verifier are stated against the predicates
defined here. If this file is wrong, nothing downstream rescues us.

## Definitions

- `Lit`         — a literal `(sign, var)` where `var : Nat` is a variable index
                  and `sign : Bool` says whether the literal is positive.
- `Clause`      — a list of literals (disjunction).
- `CNF`         — a list of clauses (conjunction).
- `Assignment`  — a `List Bool` giving the value of each variable.
- `Lit.eval`    — `α[ℓ.var] = ℓ.sign` (out-of-range reads as `false`).
- `Clause.eval` — disjunction over literals.
- `CNF.eval`    — conjunction over clauses.
- `CNF.Satisfiable` — some assignment makes `CNF.eval` true.

## Out-of-range convention

A variable index `i ≥ α.length` is treated as assigned to `false`. This is
standard in SAT textbooks ("unassigned variables default to 0") and makes
the language closed under padding: a short satisfying assignment always
exists, equal to a prefix of any longer one. This is essential for
polynomial balance in the NP reduction.
-/

@[expose] public section

namespace Complexity

namespace SAT

-- ════════════════════════════════════════════════════════════════════════
-- Literals, clauses, CNF
-- ════════════════════════════════════════════════════════════════════════

/-- A literal: `sign = true` means the positive literal `x_var`;
    `sign = false` means `¬x_var`. -/
structure Lit where
  /-- Polarity of the literal: `true` for `x_var`, `false` for `¬x_var`. -/
  sign : Bool
  /-- Index of the variable this literal mentions. -/
  var : Nat
  deriving DecidableEq

/-- A clause is a disjunction of literals. The empty clause is
    unsatisfiable (an empty disjunction is `false`). -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. The empty CNF is
    satisfiable (an empty conjunction is `true`). -/
abbrev CNF := List Clause

/-- An assignment is a bit-string. Position `i` holds the value of
    variable `i`. Indices past the end read as `false`. -/
abbrev Assignment := List Bool

-- ════════════════════════════════════════════════════════════════════════
-- Evaluation
-- ════════════════════════════════════════════════════════════════════════

namespace Assignment
/-- Value of variable `i` under assignment `α`, with out-of-range = `false`. -/
@[inline] def get (α : Assignment) (i : Nat) : Bool :=
  (α[i]?).getD false
end Assignment

namespace Lit
/-- `ℓ = (s, v)` is satisfied by `α` iff `α.get v = s`. -/
@[inline] def eval (α : Assignment) (ℓ : Lit) : Bool :=
  α.get ℓ.var == ℓ.sign
end Lit

namespace Clause
/-- A clause is satisfied iff at least one literal is. -/
@[inline] def eval (α : Assignment) (c : Clause) : Bool :=
  c.any (Lit.eval α)
end Clause

namespace CNF
/-- A CNF is satisfied iff every clause is. -/
@[inline] def eval (α : Assignment) (φ : CNF) : Bool :=
  φ.all (Clause.eval α)

/-- `φ` is satisfiable if some assignment makes `CNF.eval` true. -/
def Satisfiable (φ : CNF) : Prop := ∃ α : Assignment, eval α φ = true

-- ════════════════════════════════════════════════════════════════════════
-- Basic sanity lemmas (proved here so downstream files can rely on them)
-- ════════════════════════════════════════════════════════════════════════

/-- The empty CNF evaluates to `true` (empty conjunction).
@isnad1 id=eq.0h1v.s3.86698473beb1 from=translated src=- shape=2fbd2722 vocab=5e031a58
-/
@[simp] theorem eval_nil (α : Assignment) : eval α [] = true := rfl

/-- Evaluating `c :: φ` is the conjunction of evaluating `c` and evaluating `φ`.
@isnad1 id=eq.0h3v.s4.6eaa371ca814 from=translated src=- shape=2f7a25ed vocab=dd594963
-/
@[simp] theorem eval_cons (α : Assignment) (c : Clause) (φ : CNF) :
    eval α (c :: φ) = (Clause.eval α c && eval α φ) := by
  simp [eval, List.all_cons]

/-- The empty formula is trivially satisfiable.
@isnad1 id=satisfia.0h0v.s1.aea4b8ed48ee from=translated src=- shape=87ceb31f vocab=8ca238d8
-/
theorem satisfiable_nil : Satisfiable [] := ⟨[], rfl⟩

/-- The formula `[[]]` (one empty clause) is unsatisfiable.
@isnad1 id=not.0h0v.s3.1f95c1b07b86 from=translated src=- shape=27002316 vocab=837ddc75
-/
theorem not_satisfiable_empty_clause : ¬ Satisfiable [([] : Clause)] := by
  rintro ⟨α, h⟩
  simp [eval, Clause.eval] at h

end CNF

-- ════════════════════════════════════════════════════════════════════════
-- Max variable index — used to show polynomial-length witnesses exist
-- ════════════════════════════════════════════════════════════════════════

/-- Largest variable index appearing in a literal (just `ℓ.var`). -/
@[inline] def Lit.maxVar (ℓ : Lit) : Nat := ℓ.var

/-- Largest variable index in a clause (0 if empty). -/
def Clause.maxVar : Clause → Nat
  | [] => 0
  | ℓ :: ℓs => max ℓ.var (maxVar ℓs)

/-- The empty clause has `maxVar = 0`.
@isnad1 id=eq.0h0v.s3.cd128e4e142e from=translated src=- shape=35225b15 vocab=1c16907f
-/
@[simp] theorem Clause.maxVar_nil : Clause.maxVar [] = 0 := rfl

/-- `maxVar` of `ℓ :: ℓs` is the max of `ℓ.var` and `maxVar ℓs`.
@isnad1 id=eq.0h2v.s4.6f7c3ceda184 from=translated src=- shape=1c7e4b7d vocab=25219b4e
-/
@[simp] theorem Clause.maxVar_cons (ℓ : Lit) (ℓs : Clause) :
    Clause.maxVar (ℓ :: ℓs) = max ℓ.var (Clause.maxVar ℓs) := rfl

/-- Every literal's var in a clause is at most `c.maxVar`.
@isnad1 id=le.1h2v.s4.4e983ffac2da from=translated src=- shape=78622efe vocab=7ce16f63
-/
theorem Clause.var_le_maxVar {ℓ : Lit} {c : Clause} (hℓ : ℓ ∈ c) :
    ℓ.var ≤ c.maxVar := by
  induction c with
  | nil => exact (List.not_mem_nil hℓ).elim
  | cons ℓ' ℓs ih =>
    rcases List.mem_cons.mp hℓ with h | h
    · subst h; simp
    · calc ℓ.var ≤ Clause.maxVar ℓs := ih h
        _ ≤ max ℓ'.var (Clause.maxVar ℓs) := le_max_right _ _
        _ = Clause.maxVar (ℓ' :: ℓs) := by simp

/-- Largest variable index in a CNF (0 if empty). -/
def CNF.maxVar : CNF → Nat
  | [] => 0
  | c :: cs => max c.maxVar (maxVar cs)

/-- The empty CNF has `maxVar = 0`.
@isnad1 id=eq.0h0v.s3.262dc87a3230 from=translated src=- shape=35225b15 vocab=94a604e5
-/
@[simp] theorem CNF.maxVar_nil : CNF.maxVar [] = 0 := rfl

/-- `maxVar` of `c :: cs` is the max of `c.maxVar` and `maxVar cs`.
@isnad1 id=eq.0h2v.s4.8d5914d35be4 from=translated src=- shape=1c7e4b7d vocab=f5399482
-/
@[simp] theorem CNF.maxVar_cons (c : Clause) (cs : CNF) :
    CNF.maxVar (c :: cs) = max c.maxVar (CNF.maxVar cs) := rfl

/-- Every clause's maxVar is at most `φ.maxVar`.
@isnad1 id=le.1h2v.s4.e28756cfa24d from=translated src=- shape=78622efe vocab=a9dcfdf3
-/
theorem CNF.clause_maxVar_le_maxVar {c : Clause} {φ : CNF} (hc : c ∈ φ) :
    c.maxVar ≤ φ.maxVar := by
  induction φ with
  | nil => exact (List.not_mem_nil hc).elim
  | cons c' cs ih =>
    rcases List.mem_cons.mp hc with h | h
    · subst h; simp
    · calc c.maxVar ≤ CNF.maxVar cs := ih h
        _ ≤ max c'.maxVar (CNF.maxVar cs) := le_max_right _ _
        _ = CNF.maxVar (c' :: cs) := by simp

-- ════════════════════════════════════════════════════════════════════════
-- Padding: truncating α below maxVar doesn't matter for out-of-range vars,
-- and extending α with false never changes eval.
-- ════════════════════════════════════════════════════════════════════════

/-- `Assignment.get` on `α ++ β` agrees with `α` at in-range indices.
@isnad1 id=eq.1h3v.s4.47ccb65b6200 from=translated src=- shape=e98e0629 vocab=d9ddf3c7
-/
theorem Assignment.get_append_left (α β : Assignment) (i : Nat) (h : i < α.length) :
    Assignment.get (α ++ β) i = Assignment.get α i := by
  simp only [Assignment.get, List.getElem?_append_left h]

/-- Appending to an assignment doesn't change `Lit.eval` for in-range literals.
@isnad1 id=eq.1h3v.s5.550e7a39f37c from=translated src=- shape=2829b3c8 vocab=20236f61
-/
theorem Lit.eval_append_of_lt (α β : Assignment) (ℓ : Lit) (h : ℓ.var < α.length) :
    ℓ.eval (α ++ β) = ℓ.eval α := by
  simp [Lit.eval, Assignment.get_append_left α β ℓ.var h]

-- ════════════════════════════════════════════════════════════════════════
-- Truncation: assignments agree on eval below `maxVar + 1`
-- ════════════════════════════════════════════════════════════════════════
--
-- These lemmas say that if two assignments agree on all variable positions
-- that actually appear in φ, they produce the same evaluation. In particular,
-- truncating α to length `φ.maxVar + 1` preserves `CNF.eval α φ`.
--
-- This is what powers `PolyBalanced`: given *any* satisfying α, we get a
-- short satisfying witness of length ≤ `φ.maxVar + 1 ≤ |φ.encode| + 1`.

/-- `α.get i` is preserved by truncating to any length `k > i`.
@isnad1 id=eq.1h3v.s4.32ef2ed06991 from=translated src=- shape=a5ea5ad6 vocab=19aa1b19
-/
theorem Assignment.get_take (α : Assignment) (i k : Nat) (hi : i < k) :
    Assignment.get (α.take k) i = Assignment.get α i := by
  simp only [Assignment.get]
  by_cases hl : i < α.length
  · have htl : i < (α.take k).length := by
      simp only [List.length_take]; omega
    rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem htl,
        List.getElem_take]
  · push Not at hl
    have h1 : α[i]? = none := List.getElem?_eq_none hl
    have h2 : (α.take k)[i]? = none := by
      apply List.getElem?_eq_none
      simp only [List.length_take]; omega
    rw [h1, h2]

/-- `Lit.eval` is invariant under truncation when the literal's var is in range.
@isnad1 id=eq.1h3v.s4.f9c6b201fe08 from=translated src=- shape=04d7a7f7 vocab=eff7b907
-/
theorem Lit.eval_take (α : Assignment) (ℓ : Lit) (k : Nat) (hk : ℓ.var < k) :
    Lit.eval (α.take k) ℓ = Lit.eval α ℓ := by
  simp only [Lit.eval]
  rw [Assignment.get_take α ℓ.var k hk]

/-- `Clause.eval` is preserved by truncation of α to length above `c.maxVar`.
@isnad1 id=eq.1h3v.s4.887cef3dfb78 from=translated src=- shape=04d7a7f7 vocab=5eb42692
-/
theorem Clause.eval_take (α : Assignment) (c : Clause) (k : Nat) (hk : c.maxVar < k) :
    Clause.eval (α.take k) c = Clause.eval α c := by
  induction c with
  | nil => rfl
  | cons ℓ ℓs ih =>
    simp only [maxVar_cons] at hk
    have hℓ : ℓ.var < k := by omega
    have hℓs : Clause.maxVar ℓs < k := by omega
    show ((ℓ :: ℓs).any (Lit.eval (α.take k))) = ((ℓ :: ℓs).any (Lit.eval α))
    simp only [List.any_cons, Lit.eval_take _ _ _ hℓ]
    exact congrArg _ (ih hℓs)

/-- `CNF.eval` is preserved by truncation of α to length above `φ.maxVar`.
@isnad1 id=eq.1h3v.s4.7c374d009b7f from=translated src=- shape=04d7a7f7 vocab=ab111ae2
-/
theorem CNF.eval_take (α : Assignment) (φ : CNF) (k : Nat) (hk : φ.maxVar < k) :
    CNF.eval (α.take k) φ = CNF.eval α φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [maxVar_cons] at hk
    have hc : c.maxVar < k := by omega
    have hcs : CNF.maxVar cs < k := by omega
    show ((c :: cs).all (Clause.eval (α.take k))) = ((c :: cs).all (Clause.eval α))
    simp only [List.all_cons, Clause.eval_take _ _ _ hc]
    exact congrArg _ (ih hcs)

/-- **PolyBalanced witness lemma.** A satisfiable formula has a satisfying
    assignment of length at most `φ.maxVar + 1`.
@isnad1 id=iff.0h1v.s5.72f6399cdb12 from=translated src=- shape=d390fab5 vocab=0c98fc30
-/
theorem CNF.satisfiable_iff_short_witness (φ : CNF) :
    φ.Satisfiable ↔ ∃ α : Assignment,
      α.length ≤ φ.maxVar + 1 ∧ CNF.eval α φ = true := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α.take (φ.maxVar + 1), ?_, ?_⟩
    · exact le_trans (List.length_take_le _ _) (by omega)
    · rw [CNF.eval_take α φ (φ.maxVar + 1) (by omega)]
      exact hα
  · rintro ⟨α, _, hα⟩
    exact ⟨α, hα⟩

-- ════════════════════════════════════════════════════════════════════════
-- Pointwise agreement and decidability of `Satisfiable`
-- ════════════════════════════════════════════════════════════════════════

/-- If two assignments give the same value at every index (via `Assignment.get`),
    they produce the same literal evaluation.
@isnad1 id=eq.1h3v.s4.dd074ded0fab from=translated src=- shape=ea304c80 vocab=3e5a7859
-/
theorem Lit.eval_eq_of_agree (α β : Assignment) (ℓ : Lit)
    (h : Assignment.get α ℓ.var = Assignment.get β ℓ.var) :
    Lit.eval α ℓ = Lit.eval β ℓ := by
  simp [Lit.eval, h]

/-- Pointwise agreement of `Assignment.get` implies equal `Clause.eval`.
@isnad1 id=eq.1h3v.s4.2edad7ed13f4 from=translated src=- shape=9311114d vocab=b7b83aaf
-/
theorem Clause.eval_eq_of_agree (α β : Assignment) (c : Clause)
    (h : ∀ i, Assignment.get α i = Assignment.get β i) :
    Clause.eval α c = Clause.eval β c := by
  induction c with
  | nil => rfl
  | cons ℓ ℓs ih =>
    show ((ℓ :: ℓs).any (Lit.eval α)) = ((ℓ :: ℓs).any (Lit.eval β))
    simp only [List.any_cons, Lit.eval_eq_of_agree α β ℓ (h ℓ.var)]
    exact congrArg _ ih

/-- Pointwise agreement of `Assignment.get` implies equal `CNF.eval`.
@isnad1 id=eq.1h3v.s4.521dceb02a91 from=translated src=- shape=9311114d vocab=27f6b5dd
-/
theorem CNF.eval_eq_of_agree (α β : Assignment) (φ : CNF)
    (h : ∀ i, Assignment.get α i = Assignment.get β i) :
    CNF.eval α φ = CNF.eval β φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    show ((c :: cs).all (Clause.eval α)) = ((c :: cs).all (Clause.eval β))
    simp only [List.all_cons, Clause.eval_eq_of_agree α β c h]
    exact congrArg _ ih

/-- Appending `false`s doesn't change `Assignment.get`: out-of-range positions
    default to `false` anyway.
@isnad1 id=eq.0h3v.s4.f9e0165bdf14 from=translated src=- shape=c6a412ec vocab=95d7d660
-/
theorem Assignment.get_append_replicate_false (α : Assignment) (k i : Nat) :
    Assignment.get (α ++ List.replicate k false) i = Assignment.get α i := by
  simp only [Assignment.get]
  by_cases hi : i < α.length
  · rw [List.getElem?_append_left hi]
  · push Not at hi
    rw [List.getElem?_eq_none hi]
    by_cases hi' : i < α.length + k
    · rw [List.getElem?_append_right hi]
      have hrepl : (i - α.length) < (List.replicate k false : List Bool).length := by
        simp; omega
      rw [List.getElem?_eq_getElem hrepl]
      simp [List.getElem_replicate]
    · push Not at hi'
      rw [List.getElem?_eq_none (by simp; omega)]

/-- Padding an assignment with `false`s doesn't change `CNF.eval`.
@isnad1 id=eq.0h3v.s4.0479423bd1d3 from=translated src=- shape=cfc26794 vocab=410135d4
-/
theorem CNF.eval_append_replicate_false (α : Assignment) (k : Nat) (φ : CNF) :
    CNF.eval (α ++ List.replicate k false) φ = CNF.eval α φ :=
  CNF.eval_eq_of_agree _ _ _ (fun _ => Assignment.get_append_replicate_false α k _)

/-- **Brute-force decidability.** Satisfiability is decidable by enumerating
    all `2^(φ.maxVar + 1)` assignments of length `φ.maxVar + 1`. Not
    poly-time, but establishes that the semantic layer is concretely
    computable and enables `decide` on small instances. -/
instance CNF.decidableSatisfiable (φ : CNF) : Decidable φ.Satisfiable := by
  suffices h : φ.Satisfiable ↔
      ∃ f : Fin (φ.maxVar + 1) → Bool, CNF.eval (List.ofFn f) φ = true from
    decidable_of_iff _ h.symm
  rw [CNF.satisfiable_iff_short_witness]
  constructor
  · rintro ⟨α, hlen, heval⟩
    -- Pad α with `false`s up to length `maxVar + 1`, then identify with a Fin-indexed function.
    let α' : Assignment := α ++ List.replicate (φ.maxVar + 1 - α.length) false
    have hα'_len : α'.length = φ.maxVar + 1 := by
      simp only [α', List.length_append, List.length_replicate]; omega
    refine ⟨fun i => α'[i.val]'(by rw [hα'_len]; exact i.isLt), ?_⟩
    rw [← CNF.eval_append_replicate_false α (φ.maxVar + 1 - α.length) φ] at heval
    change CNF.eval α' φ = true at heval
    -- List.ofFn (fun i => α'[i.val]) agrees pointwise with α' via Assignment.get,
    -- so CNF.eval is the same.
    rw [CNF.eval_eq_of_agree _ α' φ (fun i => ?_)]
    · exact heval
    · simp only [Assignment.get]
      by_cases hi : i < φ.maxVar + 1
      · have h1 : i < (List.ofFn (fun j : Fin (φ.maxVar + 1) =>
            α'[j.val]'(by rw [hα'_len]; exact j.isLt))).length := by simp [hi]
        have hi' : i < α'.length := by rw [hα'_len]; exact hi
        rw [List.getElem?_eq_getElem h1, List.getElem_ofFn,
            List.getElem?_eq_getElem hi']
      · push Not at hi
        rw [List.getElem?_eq_none (by simp; omega),
            List.getElem?_eq_none (by rw [hα'_len]; exact hi)]
  · rintro ⟨f, hf⟩
    exact ⟨List.ofFn f, by simp, hf⟩

/-- Evaluating a concatenation of clauses is the disjunction of the evaluations.
@isnad1 id=eq.0h3v.s4.2ebb62b6bf8d from=translated src=- shape=ca695f77 vocab=dd7ab427
-/
@[simp] theorem Clause.eval_append (α : Assignment) (c d : Clause) :
    Clause.eval α (c ++ d) = (Clause.eval α c || Clause.eval α d) := by
  induction c with
  | nil => simp [Clause.eval]
  | cons _ _ _ => simp [Clause.eval, List.any_cons, Bool.or_assoc]

/-- Evaluating a concatenation of CNFs is the conjunction of the evaluations.
@isnad1 id=eq.0h3v.s4.5da64b033562 from=translated src=- shape=ca695f77 vocab=377cc1a8
-/
@[simp] theorem CNF.eval_append (α : Assignment) (φ ψ : CNF) :
    CNF.eval α (φ ++ ψ) = (CNF.eval α φ && CNF.eval α ψ) := by
  induction φ with
  | nil => simp [CNF.eval]
  | cons _ _ _ => simp [CNF.eval, List.all_cons, Bool.and_assoc]

end SAT

end Complexity
