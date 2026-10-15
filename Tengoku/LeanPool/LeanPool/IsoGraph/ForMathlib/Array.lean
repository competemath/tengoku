/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku

/-!
# Lemmas about arrays and `getElem!`

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

@[expose] public section

/--
@isnad1 id=eq.2h3v.s6.528d5fa8b8f0 from=translated src=- shape=c5f3a17a vocab=a4971b94
-/
theorem array_extD {α : Type _} [Inhabited α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  refine Array.ext hs fun i hi hi' => ?_
  have := h i hi
  rwa [getElem!_pos a i hi, getElem!_pos b i hi'] at this

/--
@isnad1 id=iff.0h2v.s5.085487f96f60 from=translated src=- shape=056ccebb vocab=cad39d64
-/
theorem mem_iff_getElemD {a : Array Nat} {v : Nat} : v ∈ a ↔ ∃ i, i < a.size ∧ a[i]! = v := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
    exact ⟨i, hi, by rw [getElem!_pos a i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    rw [getElem!_pos a i hi]
    exact Array.getElem_mem hi

/-- An in-bounds `getElem!` is a member.
@isnad1 id=mem.1h2v.s5.93bc22ea8b93 from=translated src=- shape=557be56f vocab=cad39d64
-/
theorem getElemD_mem {a : Array Nat} {j : Nat} (h : j < a.size) : a[j]! ∈ a := by
  rw [getElem!_pos a j h]
  exact Array.getElem_mem h

/-- Reading one entry of `Array.set!`, the only fact about it these proofs need.
@isnad1 id=eq.1h5v.s6.50c3437e88f9 from=translated src=- shape=6065134b vocab=60f72fbe
-/
theorem getElemD_setD {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (hi : i < a.size) (k : Nat) :
    (a.set! i x)[k]! = if k = i then x else a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk, eq_comm (a := i)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk,
      ite_eq_right (by omega)]

/-- Companion to `getElemD_setD` for the off-diagonal case, where no bound on `i` is needed:
writing at `i` never disturbs another index, in bounds or not.
@isnad1 id=eq.1h5v.s6.74309bc04eda from=translated src=- shape=a67ef831 vocab=515a17fb
-/
theorem getElemD_setD_ne {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α} {k : Nat}
    (h : k ≠ i) :
    (a.set! i x)[k]! = a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk,
      ite_eq_right (Ne.symm h)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk]

/-- Distinct positions of a duplicate-free array hold distinct values.
@isnad1 id=ne.4h3v.s6.a4dc4384fb31 from=translated src=- shape=1cbcbac6 vocab=a6851f87
-/
theorem nodup_getElemD_ne {a : Array Nat} (h : a.toList.Nodup) {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) (hij : i ≠ j) : a[i]! ≠ a[j]! := by
  rw [getElem!_pos a i hi, getElem!_pos a j hj]
  intro he
  exact hij ((List.Nodup.getElem_inj_iff h).mp he)

/-- An array whose entries at distinct indices differ has no duplicates.
@isnad1 id=nodup.1h1v.s6.08696edb5b02 from=translated src=- shape=21454a15 vocab=a6851f87
-/
theorem nodup_of_getElemD_ne {a : Array Nat}
    (h : ∀ i j, i < a.size → j < a.size → i < j → a[i]! ≠ a[j]!) : a.toList.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < a.size := by simpa using hi
  have hj' : j < a.size := by simpa using hj
  have := h i j hi' hj' hij
  rwa [getElem!_pos a i hi', getElem!_pos a j hj'] at this

/--
@isnad1 id=le.3h3v.s6.e57d4a463ad8 from=translated src=- shape=514ac5e4 vocab=eb23e3a4
-/
theorem pairwise_getElemD_le {a : Array Nat} (hp : a.toList.Pairwise (· ≤ ·)) {i j : Nat}
    (hj : j < a.size) (hij : i ≤ j) : a[i]! ≤ a[j]! := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_refl _
  · have hi : i < a.size := by omega
    have := List.pairwise_iff_getElem.1 hp i j (by simpa using hi) (by simpa using hj) h
    rwa [getElem!_pos a i hi, getElem!_pos a j hj, ← Array.getElem_toList, ← Array.getElem_toList]

/--
@isnad1 id=lt.4h3v.s6.5781715aee6c from=translated src=- shape=74d9137e vocab=e85174a8
-/
theorem pairwise_getElemD_lt {a : Array Nat} (hp : a.toList.Pairwise (· ≤ ·))
    (hnd : a.toList.Nodup) {i j : Nat} (hj : j < a.size) (hij : i < j) : a[i]! < a[j]! := by
  have hi : i < a.size := by omega
  have hle : a[i]! ≤ a[j]! := by
    have := List.pairwise_iff_getElem.1 hp i j (by simpa using hi) (by simpa using hj) hij
    rwa [getElem!_pos a i hi, getElem!_pos a j hj, ← Array.getElem_toList, ← Array.getElem_toList]
  exact lt_of_le_of_ne hle (nodup_getElemD_ne hnd hi hj (by omega))

/--
@isnad1 id=iff.0h1v.s4.719d7b7fb5ab from=translated src=- shape=c7042e6b vocab=e36d826b
-/
theorem arr_isEmpty_iff (a : Array Nat) : a.isEmpty = true ↔ ∀ x, x ∉ a := by
  rw [Array.isEmpty_iff]
  constructor
  · intro h x hx
    rw [h] at hx
    simp at hx
  · intro h
    exact Array.ext' (List.eq_nil_iff_forall_not_mem.2 fun x hx => h x (by simpa using hx))

/--
@isnad1 id=eq.0h3v.s5.309761b84a9a from=translated src=- shape=1bc769b1 vocab=4d3fd05e
-/
theorem push_getElemD_eq {α : Type} [Inhabited α] (a : Array α) (v : α) :
    (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by rw [Array.size_push]; omega)]
  simp

/--
@isnad1 id=eq.1h4v.s6.c97b58a042f2 from=translated src=- shape=39fc0142 vocab=4d3fd05e
-/
theorem push_getElemD_lt {α : Type} [Inhabited α] (a : Array α) (v : α) {i : Nat}
    (hi : i < a.size) : (a.push v)[i]! = a[i]! := by
  rw [getElem!_pos (a.push v) i (by rw [Array.size_push]; omega), getElem!_pos a i hi,
    Array.getElem_push_lt hi]

/--
@isnad1 id=eq.0h1v.s4.e66a8fcd280e from=translated src=- shape=59792fa1 vocab=03bb4375
-/
theorem extract_self (a : Array Nat) : a.extract 0 a.size = a := by
  apply Array.ext'; simp

/--
@isnad1 id=eq.1h2v.s4.937b80f2684a from=translated src=- shape=0cec2dcb vocab=0a23ddc4
-/
theorem extract_size {a : Array Nat} {j : Nat} (hj : j ≤ a.size) : (a.extract 0 j).size = j := by
  simp; omega

/--
@isnad1 id=eq.1h3v.s6.ef08e1335f7c from=translated src=- shape=eeb348dd vocab=355f88e5
-/
theorem extract_getElemD {a : Array Nat} {j i : Nat} (hi : i < j) :
    (a.extract 0 j)[i]! = a[i]! := by
  rcases Nat.lt_or_ge i a.size with h | h
  · rw [getElem!_pos (a.extract 0 j) i (by simp; omega), getElem!_pos a i h]
    simp
  · rw [getElem!_neg (a.extract 0 j) i (by simp; omega), getElem!_neg a i (by omega)]

/--
@isnad1 id=eq.1h3v.s5.4705bb945554 from=translated src=- shape=8c89a06d vocab=7a58cc97
-/
theorem push_extract {a : Array Nat} {v j : Nat} (hj : j ≤ a.size) :
    (a.push v).extract 0 j = a.extract 0 j := by
  apply Array.ext'
  simp only [Array.toList_extract, Array.toList_push, List.extract_eq_take_drop, Nat.sub_zero,
    List.drop_zero]
  rw [List.take_append_of_le_length (by simpa using hj)]

/--
@isnad1 id=eq.3h3v.s6.788a3ebff96d from=translated src=- shape=7cdde5cb vocab=81a836cd
-/
theorem take_toList_eq {a b : Array Nat} {j : Nat} (hja : j ≤ a.size) (hjb : j ≤ b.size)
    (h : ∀ k, k < j → a[k]! = b[k]!) : a.toList.take j = b.toList.take j := by
  refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
  simp only [List.length_take, Array.length_toList, Nat.lt_min] at hk1
  have hka : k < a.toList.length := by simp; omega
  have hkb : k < b.toList.length := by simp; omega
  rw [List.getElem_take, List.getElem_take,
    show a.toList[k] = a[k]! by rw [getElem!_pos a k (by simpa using hka)]; simp,
    show b.toList[k] = b[k]! by rw [getElem!_pos b k (by simpa using hkb)]; simp]
  exact h k hk1.1

/--
@isnad1 id=eq.0h2v.s5.f766fbf19420 from=translated src=- shape=917bc6de vocab=9248f30c
-/
theorem replicate_getElemD_false {n w : Nat} : (Array.replicate n false)[w]! = false := by
  by_cases h : w < n
  · rw [getElem!_pos (Array.replicate n false) w (by simpa using h)]; simp
  · rw [getElem!_neg (Array.replicate n false) w (by simpa using h)]; rfl
