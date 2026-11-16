/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Tengoku.Seed.Data.ENat.Lattice
public import Tengoku.FactorizationTheoryFormalization.FactorizationTheory.Mathlib.RingTheory.Factorization.Monoid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal and minimal factorization lengths

This file defines the `ℕ∞`-valued maximal and minimal factorization lengths of an element of a
commutative monoid, develops their elementary API, and characterizes bounded factorization monoids
in terms of the maximal length.

## Main results

* `boundedFactorizationMonoid_iff_forall_maxFactorizationLength_ne_top`: a monoid is a
  BF-monoid iff it is atomic and every nonzero element has finite maximal length.
* `maxFactorizationLength_eq_minFactorizationLength_iff`: for a nonempty set of factorization
  lengths, the two extrema agree exactly when the set is a subsingleton.

## Implementation notes

If `a` has no factorization, its maximal length is `0` and its minimal length is `⊤`. Taking
`sSup` and `sInf` after mapping into `ℕ∞` records an unbounded set of lengths as `⊤`, rather
than using the fallback value `0` of `Nat.sSup`.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public noncomputable section
namespace Tengoku.FactorizationTheoryFormalization end Tengoku.FactorizationTheoryFormalization open Tengoku.FactorizationTheoryFormalization 
assert_not_exists Field Ideal

variable {α : Type*}

section CommMonoid

variable [CommMonoid α] {a b : α}

/-- The maximal length of a factorization of `a` into irreducibles, as an element of `ℕ∞`.
If `a` has unbounded factorization lengths this is `⊤`; if `a` has no factorization it
is `0`.-/
def _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength (a : α) : ℕ∞ :=
  sSup (((↑) : ℕ → ℕ∞) '' factorizationLengths a)

/--
@isnad1 id=eq.0h2v.s5.2e5164d67e83 from=translated src=- shape=5a9abcd3 vocab=2dfe5d2d
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength_def :
    maxFactorizationLength a = sSup (((↑) : ℕ → ℕ∞) '' factorizationLengths a) := by
  rfl

/-- The minimal length of a factorization of `a` into irreducibles, as an element of `ℕ∞`.
If `a` has no factorization it is `⊤`.-/
def _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength (a : α) : ℕ∞ :=
  sInf (((↑) : ℕ → ℕ∞) '' factorizationLengths a)

/--
@isnad1 id=eq.0h2v.s5.c2605371ff6d from=translated src=- shape=5a9abcd3 vocab=7f7f18ec
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength_def :
    minFactorizationLength a = sInf (((↑) : ℕ → ℕ∞) '' factorizationLengths a) := by
  rfl

/--
@isnad1 id=eq.1h3v.s4.3301c375aa9d from=translated src=- shape=397ee572 vocab=79399ad2
-/
theorem Associated.maxFactorizationLength_eq (h : Associated a b) :
    maxFactorizationLength a = maxFactorizationLength b := by
  rw [maxFactorizationLength_def, maxFactorizationLength_def, h.factorizationLengths_eq]

/--
@isnad1 id=eq.1h3v.s4.f0143270787a from=translated src=- shape=397ee572 vocab=22d47980
-/
theorem Associated.minFactorizationLength_eq (h : Associated a b) :
    minFactorizationLength a = minFactorizationLength b := by
  rw [minFactorizationLength_def, minFactorizationLength_def, h.factorizationLengths_eq]

/--
@isnad1 id=eq.1h2v.s5.518a2d34e56e from=translated src=- shape=a0ed7a64 vocab=c56aba02
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength_of_factorizations_eq_empty (h : factorizations a = ∅) :
    maxFactorizationLength a = 0 := by
  rw [maxFactorizationLength, factorizationLengths_def, h, Set.image_empty, Set.image_empty,
    sSup_empty, bot_eq_zero]

/--
@isnad1 id=eq.1h2v.s5.86c8cabcc668 from=translated src=- shape=0725423f vocab=736891da
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength_of_factorizations_eq_empty (h : factorizations a = ∅) :
    minFactorizationLength a = ⊤ := by
  rw [minFactorizationLength, factorizationLengths_def, h, Set.image_empty, Set.image_empty,
    sInf_empty]

/--
@isnad1 id=eq.1h2v.s4.ed71a46f2859 from=translated src=- shape=10a88c7d vocab=41be6ed1
-/
@[simp]
theorem _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength_of_isUnit (h : IsUnit a) : maxFactorizationLength a = 0 := by
  rw [maxFactorizationLength, factorizationLengths_of_isUnit h, Set.image_singleton,
    sSup_singleton, Nat.cast_zero]

/--
@isnad1 id=eq.1h2v.s4.b306792d2933 from=translated src=- shape=10a88c7d vocab=5a766f9f
-/
@[simp]
theorem _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength_of_isUnit (h : IsUnit a) : minFactorizationLength a = 0 := by
  rw [minFactorizationLength, factorizationLengths_of_isUnit h, Set.image_singleton,
    sInf_singleton, Nat.cast_zero]

/--
@isnad1 id=eq.1h2v.s4.289eba482fd3 from=translated src=- shape=10a88c7d vocab=680dc653
-/
@[simp]
theorem _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength_of_irreducible (h : Irreducible a) :
    maxFactorizationLength a = 1 := by
  rw [maxFactorizationLength, factorizationLengths_of_irreducible h, Set.image_singleton,
    sSup_singleton, Nat.cast_one]

/--
@isnad1 id=eq.1h2v.s4.6216449764f9 from=translated src=- shape=10a88c7d vocab=2a342f69
-/
@[simp]
theorem _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength_of_irreducible (h : Irreducible a) :
    minFactorizationLength a = 1 := by
  rw [minFactorizationLength, factorizationLengths_of_irreducible h, Set.image_singleton,
    sInf_singleton, Nat.cast_one]

/--
@isnad1 id=le.1h2v.s4.69731504c232 from=translated src=- shape=f3b0a781 vocab=2bd64758
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength_le_maxFactorizationLength
    (h : (factorizationLengths a).Nonempty) :
    minFactorizationLength a ≤ maxFactorizationLength a :=
  sInf_le_sSup (h.image _)

/--
@isnad1 id=iff.0h2v.s4.72a40a1d0f6e from=translated src=- shape=4527f4bd vocab=497ae33b
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength_ne_top_iff :
    maxFactorizationLength a ≠ ⊤ ↔ BddAbove (factorizationLengths a) := by
  rw [maxFactorizationLength, Set.image_eq_range, sSup_range, ENat.iSup_natCast_ne_top,
    Subtype.range_coe]

/-- The maximal factorization length of an element with nonempty, bounded lengths is attained.
@isnad1 id=ex.2h2v.s5.9b1e1973700a from=translated src=- shape=265b2b9e vocab=88f6e807
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.exists_natCast_eq_maxFactorizationLength (hne : (factorizationLengths a).Nonempty)
    (hbdd : BddAbove (factorizationLengths a)) :
    ∃ n ∈ factorizationLengths a, (n : ℕ∞) = maxFactorizationLength a := by
  refine ⟨sSup (factorizationLengths a), Nat.sSup_mem hne hbdd, ?_⟩
  rw [maxFactorizationLength, sSup_image]
  exact ENat.natCast_sSup hbdd

/-- The minimal factorization length of an element with a factorization is attained.
@isnad1 id=ex.1h2v.s5.df979528db54 from=translated src=- shape=e747891f vocab=de428181
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.exists_natCast_eq_minFactorizationLength (hne : (factorizationLengths a).Nonempty) :
    ∃ n ∈ factorizationLengths a, (n : ℕ∞) = minFactorizationLength a := by
  refine ⟨sInf (factorizationLengths a), Nat.sInf_mem hne, ?_⟩
  rw [minFactorizationLength, sInf_image]
  exact ENat.natCast_sInf hne

/-- For a nonempty set of factorization lengths, its maximal and minimal lengths agree if and only
if it is a subsingleton.
@isnad1 id=iff.1h2v.s4.954eb87d6f4c from=translated src=- shape=fb51104f vocab=6d53b9f1
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.maxFactorizationLength_eq_minFactorizationLength_iff
    (hne : (factorizationLengths a).Nonempty) :
    maxFactorizationLength a = minFactorizationLength a ↔
      (factorizationLengths a).Subsingleton := by
  constructor
  · intro h m hm n hn
    apply ENat.natCast_inj.mp
    apply le_antisymm
    · calc
        (m : ℕ∞) ≤ maxFactorizationLength a := by
          rw [maxFactorizationLength_def]
          exact le_sSup ⟨m, hm, rfl⟩
        _ = minFactorizationLength a := h
        _ ≤ (n : ℕ∞) := by
          rw [minFactorizationLength_def]
          exact sInf_le ⟨n, hn, rfl⟩
    · calc
        (n : ℕ∞) ≤ maxFactorizationLength a := by
          rw [maxFactorizationLength_def]
          exact le_sSup ⟨n, hn, rfl⟩
        _ = minFactorizationLength a := h
        _ ≤ (m : ℕ∞) := by
          rw [minFactorizationLength_def]
          exact sInf_le ⟨m, hm, rfl⟩
  · intro h
    obtain ⟨n, hn⟩ := hne
    rw [maxFactorizationLength_def, minFactorizationLength_def,
      h.eq_singleton_of_mem hn, Set.image_singleton, sSup_singleton, sInf_singleton]

/--
@isnad1 id=iff.0h2v.s4.4ddbf86ad756 from=translated src=- shape=b5409bd9 vocab=51564b60
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.one_le_minFactorizationLength_iff :
    1 ≤ minFactorizationLength a ↔ ¬IsUnit a := by
  rw [Order.one_le_iff_ne_zero, ne_eq, minFactorizationLength, ENat.sInf_eq_zero]
  simp [zero_mem_factorizationLengths_iff]

open scoped Pointwise in
/--
@isnad1 id=le.2h3v.s5.e1c6be95a543 from=translated src=- shape=57fe164e vocab=2b4ea36b
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.le_maxFactorizationLength_mul (ha : (factorizationLengths a).Nonempty)
    (hb : (factorizationLengths b).Nonempty) :
    maxFactorizationLength a + maxFactorizationLength b ≤ maxFactorizationLength (a * b) := by
  simp only [maxFactorizationLength, sSup_image]
  exact ENat.biSup_add_biSup_le ha hb fun m hm n hn ↦
    le_iSup₂_of_le (m + n) (add_subset_factorizationLengths_mul (Set.add_mem_add hm hn))
      (Nat.cast_add m n).ge

open scoped Pointwise in
/--
@isnad1 id=le.2h3v.s5.9cdcf4fb0af8 from=translated src=- shape=abcfa077 vocab=62019595
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.minFactorizationLength_mul_le (ha : (factorizationLengths a).Nonempty)
    (hb : (factorizationLengths b).Nonempty) :
    minFactorizationLength (a * b) ≤ minFactorizationLength a + minFactorizationLength b := by
  obtain ⟨m, hm, hm'⟩ := exists_natCast_eq_minFactorizationLength ha
  obtain ⟨n, hn, hn'⟩ := exists_natCast_eq_minFactorizationLength hb
  rw [minFactorizationLength, ← hm', ← hn', ← Nat.cast_add]
  exact sInf_le ⟨m + n, add_subset_factorizationLengths_mul (Set.add_mem_add hm hn), rfl⟩

end CommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- A commutative monoid with zero is a bounded factorization monoid if and only if it is atomic
and every nonzero element has finite maximal factorization length.
@isnad1 id=iff.0h1v.s5.16d911d6795e from=translated src=- shape=736913a3 vocab=1dd9c139
-/
theorem _root_.Tengoku.FactorizationTheoryFormalization.boundedFactorizationMonoid_iff_forall_maxFactorizationLength_ne_top :
    BoundedFactorizationMonoid α ↔
      AtomicMonoid α ∧ ∀ ⦃a : α⦄, a ≠ 0 → maxFactorizationLength a ≠ ⊤ := by
  simp_rw [boundedFactorizationMonoid_iff, ← maxFactorizationLength_ne_top_iff]

end CommMonoidWithZero
-- Tengoku: root names of this library moved to Tengoku.FactorizationTheoryFormalization so they do not collide with other libraries (generated)
