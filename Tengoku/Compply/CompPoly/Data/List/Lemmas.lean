/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Gregor Mitscha-Baude
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.Nat
public import Tengoku.Seed.Data.List.GetD
public import Tengoku.Seed.Data.List.Nodup
public import Tengoku.Seed.Order.Lattice.Nat
public import Tengoku.Seed.Tactic.Cases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auxiliary lemmas for `List`
-/

@[expose] public section
universe u v w

namespace List

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)

/--
@isnad1 id=eq.0h3v.s5.492e61eb6547 from=translated src=- shape=c22b620e vocab=b2c60b00
-/
@[simp]
theorem getLastI_append_single [Inhabited α] (x : α) : (l ++ [x]).getLastI = x := by
  simp only [List.getLastI_eq_getLast?_getD, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.getD_some]

variable {α : Type*} {unit : α}

/--
@isnad1 id=eq.1h4v.s4.22366ef81e91 from=translated src=- shape=a8896d2f vocab=7d05e07b
-/
@[simp] theorem leftpad_eq_self (l : List α) (n : Nat) (h : l.length ≥ n) :
    leftpad n unit l = l := by simp [leftpad, Nat.sub_eq_zero_of_le h]

/--
@isnad1 id=eq.0h4v.s4.be003612b0d1 from=translated src=- shape=2cb141a5 vocab=2009e9be
-/
@[simp] theorem rightpad_length (n : Nat) (unit : α) (l : List α) :
    (rightpad n unit l).length = max n l.length := by
  simp only [rightpad, length_append, length_replicate, Nat.add_comm l.length _, Nat.sub_add_eq_max]

/--
@isnad1 id=isprefix.0h4v.s4.d9ac6a63315f from=translated src=- shape=ad059612 vocab=b49b5774
-/
@[simp] theorem rightpad_prefix (n : Nat) (unit : α) (l : List α) :
    l <+: rightpad n unit l := by
  simp only [IsPrefix, rightpad]
  exact Exists.intro (replicate (n - l.length) unit) rfl

/--
@isnad1 id=issuffix.0h4v.s4.ca51339a525a from=translated src=- shape=c826a5d9 vocab=5b2a9a4e
-/
@[simp] theorem rightpad_suffix (n : Nat) (unit : α) (l : List α) :
    replicate (n - l.length) unit <:+ rightpad n unit l := by
  simp only [IsSuffix, rightpad]
  exact Exists.intro l rfl

/--
@isnad1 id=eq.1h4v.s4.93eb51ec46a7 from=translated src=- shape=58be5396 vocab=616d0023
-/
@[simp] theorem rightpad_eq_self (l : List α) (n : Nat) (h : n ≤ l.length) :
    rightpad n unit l = l := by simp [rightpad, Nat.sub_eq_zero_of_le h]

/--
@isnad1 id=eq.0h5v.s5.8cb621db0dd5 from=translated src=- shape=68fb7323 vocab=512f0e26
-/
@[simp] theorem rightpad_twice_eq_rightpad_max (m n : Nat) (unit : α) (l : List α) :
    rightpad n unit (rightpad m unit l) = rightpad (max m n) unit l := by
  rw (config := { occs := .neg [0] }) [rightpad, rightpad_length]
  simp [rightpad]
  by_cases h : m.max n ≤ l.length
  · simp [Nat.max_le.mp h]
  · refine Nat.eq_sub_of_add_eq ?_
    conv => { enter [1, 1]; rw [Nat.add_comm] }
    rw [Nat.add_assoc, Nat.sub_add_eq_max, Nat.sub_add_eq_max]
    simp at h
    by_cases h' : m ≤ l.length <;> omega

-- lemma getD_eq_getElem {l : List α} {i : Nat} {unit : α} (hi : i < l.length) :
--     l.getD i unit = l[i] := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi, Option.getD_some]

-- lemma getD_eq_default {l : List α} {i : Nat} {unit : α} (hi : i ≥ l.length) :
--     l.getD i unit = unit := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_none hi, Option.getD_none]

/--
@isnad1 id=eq.0h5v.s4.cc1afda0e7c2 from=translated src=- shape=9f93b355 vocab=132e1293
-/
@[simp] theorem rightpad_getD_eq_getD (l : List α) (n : Nat) (unit : α) (i : Nat) :
    (rightpad n unit l).getD i unit = l.getD i unit := by
  rcases (Nat.lt_or_ge i l.length) with h_lt | h_ge
  · have h_lt': i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    simp only [h_lt, h_lt', getD_eq_getElem] -- eliminate `getD`
    simp [h_lt]
  rw [getD_eq_default _ _ h_ge] -- eliminate second `getD` for `unit`
  rcases (Nat.lt_or_ge i n) with h_lt₂ | h_ge₂
  · have h_lt' : i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_getElem _ _ h_lt'] -- eliminate first `getD`
    simp [h_ge]
  · have h_ge' : i ≥ (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_default _ _ h_ge'] -- eliminate first `getD`

/-- Given two lists of potentially different lengths, right-pads the shorter list with `unit`
  elements until they are the same length.-/
def matchSize (l₁ : List α) (l₂ : List α) (unit : α) : List α × List α :=
  (l₁.rightpad (l₂.length) unit, l₂.rightpad (l₁.length) unit)

/-- `List.dropWhile` but starting from the last element. Performed by `dropWhile` on the reversed
  list, followed by a reversal.-/
def dropLastWhile (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

/-- An injective `f` separates the elements of a duplicate-free list pairwise.

This is `List.Nodup.map` transported along `List.pairwise_map`, stated in the unmapped form that
`Std.ExtTreeMap.getElem_ofList_of_mem` and friends ask for.
@isnad1 id=pairwise.2h4v.s5.df05b0ee0879 from=translated src=- shape=c01c239e vocab=bd9064b9
-/
theorem Nodup.pairwise_ne_map {α : Type u} {β : Type v} {l : List α} {f : α → β}
    (hf : Function.Injective f) (hl : l.Nodup) : l.Pairwise fun a b => f a ≠ f b :=
  List.pairwise_map.mp (Nodup.map hf hl)

end List
