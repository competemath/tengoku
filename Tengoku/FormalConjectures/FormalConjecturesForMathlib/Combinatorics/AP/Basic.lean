/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section

/-! # Arithmetic Progressions

Main definitions:
- `Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α)` : predicate asserting that `s` is the
  set consisting of an arithmetic progression of length `l` (possibly infinite) with first term
  `a` and difference `d`. Useful for cases in which additional conditions need to be applied to
  the individual terms and/or difference.
- `Set.IsAPOfLength (s : Set α) (l : ℕ∞)` : predicate asserting that `s` is the set consisting
  of an arithmetic progression of length `l`, for some some first term and difference.
-/

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `s.IsAPOfLengthWith l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/--
A list version of `Set.IsAPOfLengthWith`. Useful when order preservation is required, for example
when considering images under arbitrary functions.-/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

namespace Set.IsAPOfLengthWith

variable {s : Set α} {l : ℕ∞} {a d : α}

/-- An arithmetic progression with first term `a` and difference `d` is of length zero if and only
if `s` is empty.
@isnad1 id=iff.0h4v.s5.a889601762f1 from=translated src=- shape=f9d0107c vocab=414365cb
-/
@[simp]
theorem zero : s.IsAPOfLengthWith 0 a d ↔ s = ∅ := by simp [IsAPOfLengthWith]

/-- An arithmetic progression with first term `a` and difference `d` is of length one if and only
if `s` is a singleton.
@isnad1 id=iff.0h4v.s5.e69d552e6aff from=translated src=- shape=38c5c679 vocab=b18717e9
-/
@[simp]
theorem one : s.IsAPOfLengthWith 1 a d ↔ s = {a} := by simp +contextual [IsAPOfLengthWith]

end Set.IsAPOfLengthWith

namespace List.IsAPOfLengthWith

variable {s : List α} {l : ℕ} {a d : α}

/-- An arithmetic progression with first term `a` and difference `d` is of length zero if and only
if `s` is empty.
@isnad1 id=iff.0h4v.s4.6233b79a566a from=translated src=- shape=1f46f211 vocab=f0ad8177
-/
@[simp]
theorem zero : s.IsAPOfLengthWith 0 a d ↔ s = [] := by
  simp [IsAPOfLengthWith]

/-- An arithmetic progression with first term `a` and difference `d` is of length one if and only
if `s` is a singleton.
@isnad1 id=iff.0h4v.s5.f0c334b11441 from=translated src=- shape=87285e8b vocab=add66723
-/
@[simp]
theorem one : s.IsAPOfLengthWith 1 a d ↔ s = [a] := by
  simp [IsAPOfLengthWith]

end List.IsAPOfLengthWith

/-- In an abelian additive group `α`, the set `{a, b}` with `a ≠ b` is an arithmetic progression of
length `2` with first term `a` and difference `b - a`.
@isnad1 id=isapofle.1h3v.s5.b5dffa39669b from=translated src=- shape=763fd045 vocab=7a244be9
-/
theorem Set.isAPOfLengthWith_pair {α : Type*} [DecidableEq α] [AddCommGroup α]
    {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  simp [IsAPOfLengthWith]
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton])]
  simp
  refine Set.ext fun x => ⟨fun h ↦ ?_, fun ⟨n, ⟨_, _⟩⟩ ↦ by interval_cases n <;> simp_all⟩
  cases h with
  | inl hl => use 0; simp [hl]
  | inr hr => exact ⟨1, by norm_num, by simp_all⟩

-- Formalisation note: separate result needed for `ℕ` since this is not covered by
-- the `AddCommGroup` result above.
/-- The set `{a, b} : Set ℕ` with `a < b` is an arithmetic progression of length `2` with
first term `a` and difference `b - a`.
@isnad1 id=isapofle.1h2v.s5.e7300e8dc66c from=translated src=- shape=c403f1b7 vocab=affe4b99
-/
theorem Nat.isAPOfLengthWith_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hab
  simp [Set.IsAPOfLengthWith, h, add_assoc]
  exact Set.ext fun x => ⟨fun a => by aesop, fun ⟨w, ⟨_, _⟩⟩ => by interval_cases w <;> simp_all⟩

/--
The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite).
This predicate does not assert a specific value for the first term or the difference of the
arithmetic progression.-/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/--
A list version of `Set.IsAPOfLength`. Useful when order preservation is required, for example
when considering images under arbitrary functions.-/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Set.IsAPOfLength

open Set.IsAPOfLengthWith

variable {s : Set α} {l : ℕ∞}

/--
@isnad1 id=eq.1h3v.s4.0e4f6697bc6c from=translated src=- shape=1c853247 vocab=1aff8101
-/
theorem card (h : s.IsAPOfLength l) : ENat.card s = l := h.choose_spec.choose_spec.1

/-- Only the empty set is a finite arithmetic progression of length $0$.
@isnad1 id=iff.0h2v.s4.b705fc57c376 from=translated src=- shape=193be9db vocab=5cb027d1
-/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = ∅ := by simp [Set.IsAPOfLength]

/-- Only singletons are finite arithmetic progressions of length $1$.
@isnad1 id=iff.0h2v.s5.71e2c289f91a from=translated src=- shape=70e3345a vocab=aa833a6a
-/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = {a} := by simp [IsAPOfLength]

/-- If a set is an arithmetic progression of lengths `l₁` and `l₂`, then the lengths are
equal.
@isnad1 id=eq.2h4v.s4.29fb13f39d33 from=translated src=- shape=16d6ee89 vocab=e7fbc537
-/
theorem congr {s : Set α} {l₁ l₂ : ℕ∞}
    (h₁ : s.IsAPOfLength l₁) (h₂ : s.IsAPOfLength l₂) :
    l₁ = l₂ := by
  rw [← h₁.card, h₂.card]

end Set.IsAPOfLength

namespace List.IsAPOfLength

open List.IsAPOfLengthWith

variable {s : List α} {l : ℕ}

/-- Only the empty list is a finite arithmetic progression of length $0$.
@isnad1 id=iff.0h2v.s4.93296875551a from=translated src=- shape=64f57b5e vocab=5b58c0e5
-/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = [] := by simp [IsAPOfLength]

/-- Only singletons are finite arithmetic progressions of length $1$.
@isnad1 id=iff.0h2v.s4.75b98ad5087e from=translated src=- shape=89a70a47 vocab=356821fa
-/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = [a] := by simp [IsAPOfLength]

end List.IsAPOfLength

/--
@isnad1 id=isapofle.1h3v.s5.cfa4921b3caa from=translated src=- shape=63491a72 vocab=5f5fcfe0
-/
theorem Set.isAPOfLength_pair {α : Type*} [DecidableEq α] [AddCommGroup α] {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLength {a, b} 2 :=
  ⟨a, b - a, Set.isAPOfLengthWith_pair hab⟩

/--
@isnad1 id=isapofle.1h2v.s5.7411c480f4e9 from=translated src=- shape=53afc463 vocab=07be3f24
-/
theorem Nat.isAPOfLength_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLength {a, b} 2 :=
  ⟨a, b - a, Nat.isAPOfLengthWith_pair hab⟩

/-- The empty set is not an arithmetic progression of positive length.
@isnad1 id=not.1h2v.s4.d3935b7c2d44 from=translated src=- shape=ab957373 vocab=43f5de9a
-/
theorem Set.not_isAPOfLength_empty {l : ℕ∞} (hl : 0 < l) :
    ¬Set.IsAPOfLength (∅ : Set α) l :=
  fun h ↦ by simp_all [h.congr <| Set.IsAPOfLength.zero.2 rfl]

/-- We say that a set `s` is free of arithmetic progressions of length `l` if `s` contains no
non-trivial arithmetic progressions of length `l`. Written as `Set.IsAPOfLengthFree s l`. --/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

/-- Any set is free of arithmetic progressions of length `1`, because such APs are all trivial.
@isnad1 id=isapofle.0h2v.s4.d4a8a732d76c from=translated src=- shape=101e930a vocab=eea256ec
-/
theorem Set.isAPOfLengthFree_one (s : Set α) : s.IsAPOfLengthFree 1 := by
  simp [Set.IsAPOfLengthFree]

/-- Any set is free of arithmetic progressions of length `0`, because such APs are all trivial.
@isnad1 id=isapofle.0h2v.s4.17c45bd5b48c from=translated src=- shape=101e930a vocab=eea256ec
-/
theorem Set.isAPOfLengthFree_zero (s : Set α) : s.IsAPOfLengthFree 0 := by
  simp [Set.IsAPOfLengthFree]

/-- Any non-trivial arithmetic progression cannot be free of arithmetic progressions.
@isnad1 id=not.2h3v.s5.81556d307a9e from=translated src=- shape=7a072b52 vocab=680dfc5c
-/
theorem Set.IsAPOfLength.not_isAPOfLengthFree {s : Set α} {l : ℕ∞}
    (hs : s.IsAPOfLength l) (hl : 1 < l) : ¬s.IsAPOfLengthFree l := by
  simpa [Set.IsAPOfLengthFree] using ⟨s, le_rfl, ⟨hs, hl⟩⟩

/--
Define the largest possible size of a subset of $\{1, \dots, N\}$ that does not contain
any non-trivial $k$-term arithmetic progression.-/
noncomputable def Set.IsAPOfLengthFree.maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}

/--
@isnad1 id=eq.0h1v.s3.0ecd997298f9 from=translated src=- shape=a60e91e3 vocab=4ffa2084
-/
theorem Set.IsAPOfLengthFree.maxCard_zero (N : ℕ) : maxCard 0 N = N := by
  simp only [maxCard, Nat.cast_zero, isAPOfLengthFree_zero, exists_const, exists_prop]
  apply IsGreatest.csSup_eq
  refine ⟨⟨Finset.Icc 1 N, Subset.rfl, Nat.card_Icc _ _⟩, ?_⟩
  rintro n ⟨S, hS, rfl⟩
  exact S.card_mono hS |>.trans_eq (Nat.card_Icc _ _)

/--
@isnad1 id=eq.0h1v.s3.3424d2fb02ee from=translated src=- shape=a60e91e3 vocab=4ffa2084
-/
theorem Set.IsAPOfLengthFree.maxCard_one (N : ℕ) : maxCard 1 N = N := by
  nth_rw 2 [← maxCard_zero N]
  simp [maxCard, isAPOfLengthFree_one, isAPOfLengthFree_zero]

/-- A set `A` contains an arithmetic progression of length `k` with difference `d`.-/
def Set.ContainsAP (A : Set α) (k : ℕ) (d : α) : Prop :=
  ∃ a, ∃ s, s ⊆ A ∧ s.IsAPOfLengthWith (k : ℕ∞) a d

def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c

/--
A function `f : β → α` has a monotone `k`-term arithmetic progression if there exists a choice
of indices `b 1 < b 2 < ... < b k` such that the subsequence `f (b i)` forms an increasing or
decreasing arithmetic progression of length `k`.-/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

/--
Define the largest possible size of a subset of a finset `s` that does not contain
any non-trivial `k`-term arithmetic progression.-/
noncomputable def Finset.maxAPFreeCard (k : ℕ) (s : Finset α) : ℕ :=
  open scoped Classical in
  (s.powerset.filter fun t : Finset α ↦ (t : Set α).IsAPOfLengthFree k).sup Finset.card
