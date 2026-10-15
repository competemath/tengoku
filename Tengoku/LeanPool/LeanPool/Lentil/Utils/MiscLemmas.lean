/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import Std.Data.HashSet.Basic
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace LentilLib

/--
@isnad1 id=iff.0h1v.s3.310711c79073 from=translated src=- shape=0bad438e vocab=54ad86a3
-/
theorem forall_unit {p : PUnit → Prop} : (∀ x, p x) ↔ p PUnit.unit := by grind

/--
@isnad1 id=iff.0h1v.s3.96defae670e1 from=translated src=- shape=32e26a05 vocab=54ad86a3
-/
theorem exists_unit {p : PUnit → Prop} : (∃ x, p x) ↔ p PUnit.unit := by grind

namespace List

/--
@isnad1 id=iff.0h3v.s6.030a31a88b6c from=translated src=- shape=f1d4ed9f vocab=d3024c1a
-/
theorem mem_forall_iff_fin_index {α : Type u} (l : List α) (p : α → Prop) :
  (∀ x, x ∈ l → p x) ↔ ∀ (x : Fin l.length), p l[x] := by
  constructor
  · intro h x; apply h; simp
  · intro h x hin; rw [List.mem_iff_getElem] at hin
    rcases hin with ⟨n, hlt, heq⟩; subst_vars; exact h ⟨_, hlt⟩

/--
@isnad1 id=iff.0h3v.s6.9cdb277a1448 from=translated src=- shape=0228da30 vocab=d3024c1a
-/
theorem mem_exists_iff_fin_index {α : Type u} (l : List α) (p : α → Prop) :
  (∃ x, x ∈ l ∧ p x) ↔ ∃ (x : Fin l.length), p l[x] := by
  constructor
  · intro ⟨x, hin, h⟩; rw [List.mem_iff_getElem] at hin
    rcases hin with ⟨n, hlt, heq⟩; subst_vars; exists ⟨_, hlt⟩
  · intro ⟨n, h⟩; exists l[n]; simp; try assumption

/--
@isnad1 id=mem.0h2v.s4.c0fa2b615778 from=translated src=- shape=d5a9ac66 vocab=24071927
-/
theorem finRange_fin_in (n : Nat) : ∀ (x : Fin n), x ∈ List.finRange n := by
  simp

/--
@isnad1 id=eq.1h3v.s6.35c619901391 from=translated src=- shape=1552e268 vocab=ba3a0f87
-/
theorem take_getElem_drop {α : Type u} {l : List α} {n : Nat} (h : n < l.length) :
  l.take n ++ l[n] :: l.drop (n + 1) = l := by
  conv => enter [2]; rw [← List.take_append_drop n l, ← List.getElem_cons_drop h]

/--
@isnad1 id=perm.1h4v.s6.f78d4b98f68c from=translated src=- shape=be16da42 vocab=2656c279
-/
theorem modify_perm {α : Type u} {l : List α} {idx : Nat} (h : idx < l.length) (f : α → α) :
  List.Perm (l ++ [f (l[idx]'h)]) (l.modify idx f ++ [(l[idx]'h)]) := by
  conv => enter [1, 1]; rw [← take_getElem_drop h]
  rw [List.modify_eq_take_cons_drop h]
  repeat rw [List.append_assoc]
  apply List.Perm.append; rfl
  exact List.cons_append_cons_perm

/--
@isnad1 id=and.1h4v.s6.1fd94cbb8c0e from=translated src=- shape=aa011bb0 vocab=5c966296
-/
theorem findFindIdx {α : Type u} {l : List α} {p : α → Bool} {res : α}
  (hpred : l.find? p = some res) :
  p res = true ∧ ∃ (idx : Nat) (hidx : idx < l.length), (l[idx]'hidx) = res ∧ l.findIdx? p = idx := by
  rw [List.find?_eq_some_iff_getElem] at hpred
  rcases hpred with ⟨ht, ⟨idx, hidx, rfl, h⟩⟩
  constructor
  · assumption
  · exists idx, hidx; constructor
    · rfl
    · rw [List.findIdx?_eq_some_iff_getElem]; grind

/-- Right-fold a non-empty list, returning the default `d` on the empty list. -/
def foldrD {β : Type v} (f : β → β → β) (d : β) : List β → β
  | [a] => a
  | a :: as => f a (foldrD f d as)
  | [] => d

/--
@isnad1 id=eq.1h4v.s5.1d85798fd7b0 from=translated src=- shape=c8eb0199 vocab=89db3ee0
-/
theorem foldrD_eq_foldr {β : Type v} (f : β → β → β) (d : β) (l : List β)
  (h : ∀ x, f x d = x) :
  foldrD f d l = l.foldr f d := by
  induction l with
  | nil => simp [foldrD]
  | cons a l ih =>
    rcases hh : l with _ | ⟨b, l⟩
    · simp [foldrD, h]
    · simp [foldrD, ← hh, ih]

/-- Whether a list contains a duplicate element, using hashing. -/
def containsDuplicateElemHashable {α : Type u} [BEq α] [Hashable α] (l : List α) : Bool :=
  -- NOTE: Since `MProd` assumes the same universe level for both components,
  -- `α` has to have level 1
  Prod.snd <| l.foldl (init := (Std.HashSet.emptyWithCapacity (α := α), false)) fun (seen, dup) x =>
    if dup || seen.contains x then (seen, true)
    else (seen.insert x, false)

end List

namespace Nat

-- sometimes we depend on theorems that themselves or similar ones
-- are present in Mathlib, but to reduce dependencies, we prove them here

-- NOTE: usually, the unification is not strong enough to figure out `p`,
-- which would be supplied by the user in practice
/--
@isnad1 id=ex.0h3v.s5.fc23c567c406 from=translated src=- shape=5fb2b42e vocab=6ff3cf84
-/
theorem find_min {p : Nat → Prop} (n : Nat) (h : p n) :
  ∃ n', n' ≤ n ∧ p n' ∧ ∀ m, m < n' → ¬ p m := by
  induction n using Nat.strongRecOn
  rename_i n ih
  by_cases h' : ∃ m, m < n ∧ p m
  · rcases h' with ⟨m, hlt, h'⟩
    have ⟨n', hle, ha, hb⟩ := ih _ hlt h'
    exists n'; apply And.intro (by omega) (And.intro ‹_› ‹_›)
  · simp at h'; exists n; simp_all

/--
@isnad1 id=ex.0h3v.s5.31fcf5cc8f40 from=translated src=- shape=a01e0aeb vocab=58b355c3
-/
theorem find_min' {p : Nat → Prop} (n : Nat) (h : p n) :
  ∃ n', n' ≤ n ∧ p n' ∧ ∀ m, p m → n' ≤ m := by
  have ⟨n', hn', ha, hb⟩ := find_min _ h
  exists n'; apply And.intro ‹_› (And.intro ‹_› _); intros; apply Nat.le_of_not_lt; intro hlt; solve_by_elim

end Nat

end LentilLib
