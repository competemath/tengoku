import Tengoku.ImmermanVardi.Lax979537Proofs.StackReadTable

namespace Lax979537Proofs.StackReadRelations

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- A fixed finite collection of decoder work stacks. Relation tables live
outside this collection and retain their contents between parsing steps. -/
structure Workspace (K : Type) where
  domain : K
  input : K
  count : K
  tmp : K
  rev : K
  counters : List K
  separate : [domain, input, count, tmp, rev].Nodup
  counters_nodup : counters.Nodup
  counter_fresh : ∀ c ∈ counters, c ∉ [domain, input, count, tmp, rev]

def Fresh (w : Workspace K) (table : K) : Prop :=
  table ∉ [w.domain, w.input, w.count, w.tmp, w.rev] ∧ table ∉ w.counters

def Ready (w : Workspace K) (n : Nat) (s : BitStore K (Aux × Bool)) : Prop :=
  s.stk w.domain = List.replicate n true ∧ s.stk w.tmp = [] ∧ s.stk w.count = [] ∧
    s.stk w.rev = [] ∧ ∀ c ∈ w.counters, s.stk c = []

def oneTable (w : Workspace K) (arity : Nat) (table : K) : BitProgram K (Aux × Bool) :=
  StackReadTable.readTable w.domain w.input table w.count w.tmp w.rev (w.counters.take arity)

/--
@isnad1 id=ready.2h7v.s5.6c742a0467ac from=translated src=- shape=1ad6077c vocab=37bfcdf5
-/
theorem result_ready (w : Workspace K) (table : K) (hf : Fresh w table)
    (n arity : Nat) (s : BitStore K (Aux × Bool)) (hs : Ready w n s) :
    Ready w n (StackReadTable.result w.input table n arity s) := by
  have hcore := w.separate
  have htable := hf.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hcore htable
  have hp (c : K) (hi : c ≠ w.input) (ht : c ≠ table) :
      (StackReadTable.result w.input table n arity s).stk c = s.stk c :=
    StackReadTable.result_preserves _ _ _ hi ht _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hp w.domain (by tauto) (by tauto)]; exact hs.1
  · rw [hp w.tmp (by tauto) (by tauto)]; exact hs.2.1
  · rw [hp w.count (by tauto) (by tauto)]; exact hs.2.2.1
  · rw [hp w.rev (by tauto) (by tauto)]; exact hs.2.2.2.1
  · intro c hm
    have h := w.counter_fresh c hm
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
    have hct : c ≠ table := fun he => hf.2 (he ▸ hm)
    rw [hp c (by tauto) hct]
    exact hs.2.2.2.2 c hm

def readTables (w : Workspace K) : List (Nat × K) → BitProgram K (Aux × Bool)
  | [] => .atom (.load (fun s => (s.1, none)))
  | (arity, table) :: rest => .seq (oneTable w arity table) (readTables w rest)

def result (w : Workspace K) (n : Nat) : List (Nat × K) →
    BitStore K (Aux × Bool) → BitStore K (Aux × Bool)
  | [], s => ⟨(s.state.1, none), s.stk⟩
  | (arity, table) :: rest, s =>
      result w n rest (StackReadTable.result w.input table n arity s)

noncomputable def costPolynomial : List (Nat × K) → Polynomial Nat
  | [] => Polynomial.C 1
  | (arity, _) :: rest => StackReadTable.costPolynomial arity + costPolynomial rest

def cost : List (Nat × K) → Nat → Nat
  | [], _ => 1
  | (arity, _) :: rest, n => StackReadTable.cost arity n + cost rest n

omit [DecidableEq K] in
/--
@isnad1 id=eq.0h3v.s4.5c9d9fa06941 from=translated src=- shape=cba51b48 vocab=24107c48
-/
theorem eval_costPolynomial (tables : List (Nat × K)) (n : Nat) :
    (costPolynomial tables).eval n = cost tables n := by
  induction tables with
  | nil => simp [costPolynomial, cost]
  | cons r rest ih => cases r; simp [costPolynomial, cost, StackReadTable.eval_costPolynomial, ih]

/--
@isnad1 id=eq.2h7v.s6.bcd56dcde36b from=translated src=- shape=88a8d741 vocab=b04d0b40
-/
theorem result_preserves (w : Workspace K) (n : Nat) (tables : List (Nat × K))
    (key : K) (hi : key ≠ w.input) (ht : ∀ r ∈ tables, key ≠ r.2)
    (s : BitStore K (Aux × Bool)) : (result w n tables s).stk key = s.stk key := by
  induction tables generalizing s with
  | nil => rfl
  | cons r rest ih =>
      obtain ⟨arity, table⟩ := r
      rw [result, ih (fun r hm => ht r (by simp [hm]))]
      exact StackReadTable.result_preserves _ _ _ hi (ht (arity, table) (by simp)) _ _ _

/--
@isnad1 id=ready.2h6v.s6.d1567d834b7b from=translated src=- shape=77baab49 vocab=6e5320e8
-/
theorem tables_ready (w : Workspace K) (n : Nat) (tables : List (Nat × K))
    (hf : ∀ r ∈ tables, Fresh w r.2) (s : BitStore K (Aux × Bool)) (hs : Ready w n s) :
    Ready w n (result w n tables s) := by
  induction tables generalizing s with
  | nil => exact hs
  | cons r rest ih =>
      obtain ⟨arity, table⟩ := r
      exact ih (fun r hm => hf r (by simp [hm])) _
        (result_ready w table (hf (arity, table) (by simp)) n arity s hs)

/--
@isnad1 id=le.1h6v.s6.097b6c9893d7 from=translated src=- shape=ec439626 vocab=5d896aa5
-/
theorem input_length_le (w : Workspace K) (n : Nat) (tables : List (Nat × K))
    (hf : ∀ r ∈ tables, Fresh w r.2) (s : BitStore K (Aux × Bool)) :
    ((result w n tables s).stk w.input).length ≤ (s.stk w.input).length := by
  induction tables generalizing s with
  | nil => exact le_refl _
  | cons r rest ih =>
      obtain ⟨arity, table⟩ := r
      have h := ih (fun r hm => hf r (by simp [hm])) (StackReadTable.result w.input table n arity s)
      have hi : w.input ≠ table := by
        have hf' := (hf (arity, table) (by simp)).1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hf'
        tauto
      simp only [StackReadTable.result, Function.update_of_ne hi, Function.update_self,
        List.length_drop] at h
      exact h.trans (Nat.sub_le _ _)

end Lax979537Proofs.StackReadRelations
