/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1991, Problem 3

Let S = {1, 2, ..., 280}. Find the smallest natural number n such
that every n-element subset of S contains five numbers which are
pairwise relatively prime.
-/

namespace Imo1991P3

abbrev solution : ℕ := 217

/-- The elements of `{1, ..., 280}` divisible by `2`, `3`, `5` or `7`.
Among any five of them, two share a common prime factor. -/
def badSet : Finset ℕ := (Finset.Icc 1 280).filter fun x => 2 ∣ x ∨ 3 ∣ x ∨ 5 ∣ x ∨ 7 ∣ x

/-- `1` together with all primes in `{1, ..., 280}`; pairwise coprime. -/
def coprimeSet1 : Finset ℕ :=
  {1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
   179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269,
   271, 277}

/-- `{2·41, 3·37, 5·31, 7·29, 11·23, 13·19}`; pairwise coprime. -/
def coprimeSet2 : Finset ℕ := {82, 111, 155, 203, 253, 247}

/-- `{2·37, 3·31, 5·29, 7·23, 11·19, 13·17}`; pairwise coprime. -/
def coprimeSet3 : Finset ℕ := {74, 93, 145, 161, 209, 221}

/-- `{2·31, 3·29, 5·23, 7·19, 11·17, 13·13}`; pairwise coprime. -/
def coprimeSet4 : Finset ℕ := {62, 87, 115, 133, 187, 169}

/-- `{2·29, 3·23, 5·19, 7·17, 11·13}`; pairwise coprime. -/
def coprimeSet5 : Finset ℕ := {58, 69, 95, 119, 143}

/-- `{2·23, 3·19, 5·17, 7·13, 11·11}`; pairwise coprime. -/
def coprimeSet6 : Finset ℕ := {46, 57, 85, 91, 121}

/-- The union of the six pairwise coprime families, all inside `{1, ..., 280}`. -/
def bigUnion : Finset ℕ :=
  coprimeSet1 ∪ coprimeSet2 ∪ coprimeSet3 ∪ coprimeSet4 ∪ coprimeSet5 ∪ coprimeSet6

set_option maxRecDepth 1000 in
/--
@isnad1 id=eq.0h0v.s3.aa5d8c264297 from=translated src=- shape=3701a056 vocab=14b3bd87
-/
lemma bigUnion_card : bigUnion.card = 88 := by decide

set_option maxRecDepth 1000 in
/--
@isnad1 id=mem.1h1v.s5.e9eb650e7d9b from=translated src=- shape=b3c5760c vocab=143ca15c
-/
lemma bigUnion_subset : ∀ x ∈ bigUnion, x ∈ Finset.Icc 1 280 := by decide

set_option maxRecDepth 1000 in
/--
@isnad1 id=eq.3h2v.s5.5cb5d8fcef6e from=translated src=- shape=e37d1e59 vocab=c758a1e9
-/
lemma coprimeSet1_pairwise :
    ∀ a ∈ coprimeSet1, ∀ b ∈ coprimeSet1, a ≠ b → Nat.gcd a b = 1 := by decide

/--
@isnad1 id=eq.3h2v.s5.9daaf48c1a0c from=translated src=- shape=e37d1e59 vocab=081fcd9e
-/
lemma coprimeSet2_pairwise :
    ∀ a ∈ coprimeSet2, ∀ b ∈ coprimeSet2, a ≠ b → Nat.gcd a b = 1 := by decide

/--
@isnad1 id=eq.3h2v.s5.ad49a758ea42 from=translated src=- shape=e37d1e59 vocab=6eec05ec
-/
lemma coprimeSet3_pairwise :
    ∀ a ∈ coprimeSet3, ∀ b ∈ coprimeSet3, a ≠ b → Nat.gcd a b = 1 := by decide

/--
@isnad1 id=eq.3h2v.s5.7e317c019d0f from=translated src=- shape=e37d1e59 vocab=7ba2da65
-/
lemma coprimeSet4_pairwise :
    ∀ a ∈ coprimeSet4, ∀ b ∈ coprimeSet4, a ≠ b → Nat.gcd a b = 1 := by decide

/--
@isnad1 id=eq.3h2v.s5.34ad3bb2f273 from=translated src=- shape=e37d1e59 vocab=51b9040b
-/
lemma coprimeSet5_pairwise :
    ∀ a ∈ coprimeSet5, ∀ b ∈ coprimeSet5, a ≠ b → Nat.gcd a b = 1 := by decide

/--
@isnad1 id=eq.3h2v.s5.6430675757f8 from=translated src=- shape=e37d1e59 vocab=70fd63db
-/
lemma coprimeSet6_pairwise :
    ∀ a ∈ coprimeSet6, ∀ b ∈ coprimeSet6, a ≠ b → Nat.gcd a b = 1 := by decide

/-- If `P ∩ T` has at least `5` elements and the elements of `P` are pairwise coprime,
then `T` contains five pairwise coprime numbers.
@isnad1 id=ex.2h2v.s6.4cadeaf344da from=translated src=- shape=361ae4c4 vocab=ebdd0557
-/
lemma five_of_subset {T P : Finset ℕ} (h : 5 ≤ (P ∩ T).card)
    (hp : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → Nat.gcd a b = 1) :
    ∃ U ⊆ T, U.card = 5 ∧ (U : Set ℕ).Pairwise Nat.Coprime := by
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq h
  refine ⟨U, fun x hx => (Finset.mem_inter.mp (hUsub hx)).2, hUcard, ?_⟩
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  exact hp a (Finset.mem_inter.mp (hUsub ha)).1 b (Finset.mem_inter.mp (hUsub hb)).1 hab

/-- A prime in `{2, 3, 5, 7}` dividing `x`, whenever one exists. -/
def smallPrimeFactor (x : ℕ) : ℕ := if 2 ∣ x then 2 else if 3 ∣ x then 3 else if 5 ∣ x then 5 else 7

/--
@isnad1 id=mem.0h1v.s5.360f41418296 from=translated src=- shape=648617aa vocab=514deb3f
-/
lemma smallPrimeFactor_mem (x : ℕ) : smallPrimeFactor x ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  unfold smallPrimeFactor
  split_ifs <;> simp

/--
@isnad1 id=dvd.1h1v.s4.a40308b74186 from=translated src=- shape=3c98ef34 vocab=6de87b01
-/
lemma smallPrimeFactor_dvd {x : ℕ} (hx : x ∈ badSet) : smallPrimeFactor x ∣ x := by
  have hx' := Finset.mem_filter.mp hx
  unfold smallPrimeFactor
  split_ifs with h2 h3 h5
  · exact h2
  · exact h3
  · exact h5
  · rcases hx'.2 with h | h | h | h
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd h h5
    · exact h

end Imo1991P3
