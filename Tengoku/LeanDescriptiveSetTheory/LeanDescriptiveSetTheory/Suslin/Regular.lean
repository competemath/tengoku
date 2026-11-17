/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular Suslin schemes

A Suslin scheme is regular when extending its finite index can only shrink the corresponding set.
Every scheme admits a canonical regularization: at a node `s`, intersect all values indexed by
prefixes of `s`. Although the definition is written as a predicate over lists, a fixed finite list
has only finitely many prefixes, so this is exactly the classical finite-prefix intersection.

The regularized scheme is pointwise smaller, but it has exactly the same Suslin operation. The
nontrivial inclusion reuses the original branch witness and observes that every prefix of a
length-`n` initial segment is itself the initial segment at its own length.
-/

open Set

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

/-- A scheme is regular when values decrease along extension of finite indices.-/
def IsRegularSuslinScheme (A : List ℕ → Set X) : Prop :=
  ∀ ⦃s t : List ℕ⦄, s <+: t → A t ⊆ A s

/-- Intersect the values of `A` over all prefixes of `s`.

For a fixed finite list `s`, this is a finite intersection, including both `[]` and `s`.-/
def regularizeScheme (A : List ℕ → Set X) (s : List ℕ) : Set X :=
  {x | ∀ ⦃t : List ℕ⦄, t <+: s → x ∈ A t}

/-- Membership in the regularization is membership in every finite-prefix value.
@isnad1 id=iff.0h4v.s5.02a3fced8890 from=translated src=- shape=5bc902d2 vocab=a3de31c5
-/
@[simp]
theorem mem_regularizeScheme {A : List ℕ → Set X} {s : List ℕ} {x : X} :
    x ∈ regularizeScheme A s ↔ ∀ ⦃t : List ℕ⦄, t <+: s → x ∈ A t :=
  Iff.rfl

/-- Regularization is pointwise contained in the original scheme.
@isnad1 id=le.0h3v.s4.d99beb5d6f77 from=translated src=- shape=309d2bd6 vocab=fd6de17d
-/
theorem regularizeScheme_subset (A : List ℕ → Set X) (s : List ℕ) :
    regularizeScheme A s ⊆ A s := by
  intro x hx
  exact hx (List.prefix_refl s)

/-- Prefix intersections form a regular scheme.
@isnad1 id=isregula.0h2v.s3.1696db14d1f0 from=translated src=- shape=24c0e297 vocab=52cc334d
-/
theorem isRegularSuslinScheme_regularizeScheme (A : List ℕ → Set X) :
    IsRegularSuslinScheme (regularizeScheme A) := by
  intro s t hst x hx u hus
  exact hx (hus.trans hst)

/-- Regularization is monotone in the underlying scheme.
@isnad1 id=le.1h4v.s5.82fb14f72a63 from=translated src=- shape=fa6da24a vocab=fd6de17d
-/
theorem regularizeScheme_mono {A B : List ℕ → Set X} (h : ∀ s, A s ⊆ B s) (s : List ℕ) :
    regularizeScheme A s ⊆ regularizeScheme B s := by
  intro x hx t hts
  exact h t (hx hts)

/-- A regular scheme is unchanged at every node by regularization.
@isnad1 id=eq.1h3v.s4.b91427a7d6f7 from=translated src=- shape=166c5c61 vocab=52cc334d
-/
theorem IsRegularSuslinScheme.regularizeScheme_eq {A : List ℕ → Set X}
    (hA : IsRegularSuslinScheme A) (s : List ℕ) : regularizeScheme A s = A s := by
  apply Set.Subset.antisymm (regularizeScheme_subset A s)
  intro x hx t hts
  exact hA hts hx

/-- Constant schemes are fixed by regularization.
@isnad1 id=eq.0h3v.s4.0e9c8699920e from=translated src=- shape=7f6ac2c7 vocab=b2a3bab4
-/
@[simp]
theorem regularizeScheme_const (S : Set X) (s : List ℕ) :
    regularizeScheme (fun _ => S) s = S := by
  apply Set.Subset.antisymm
  · exact regularizeScheme_subset _ s
  · intro x hx t _
    exact hx

/-- The Suslin operation of the regularization is contained in the original operation.
@isnad1 id=le.0h2v.s4.bfe54dbda0ae from=translated src=- shape=569a18c8 vocab=634b6e79
-/
theorem suslinOperation_regularizeScheme_subset (A : List ℕ → Set X) :
    suslinOperation (regularizeScheme A) ⊆ suslinOperation A :=
  suslinOperation_mono fun s => regularizeScheme_subset A s

private theorem take_initialSegment (f : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (initialSegment f n).take m = initialSegment f m := by
  apply List.ext_getElem
  · simp [length_initialSegment, hmn]
  · intro i hi₁ hi₂
    simp [initialSegment]

private theorem eq_initialSegment_length_of_prefix (f : ℕ → ℕ) {s : List ℕ} {n : ℕ}
    (hs : s <+: initialSegment f n) : s = initialSegment f s.length := by
  have hlen : s.length ≤ n := by
    simpa using hs.length_le
  have htake := congrArg (List.take s.length) (List.prefix_iff_eq_append.mp hs)
  rw [List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil] at htake
  rw [take_initialSegment f hlen] at htake
  exact htake

/-- Every original Suslin witness is also a witness for the regularized scheme.
@isnad1 id=le.0h2v.s4.27b83d49bf1c from=translated src=- shape=af5800d9 vocab=634b6e79
-/
theorem suslinOperation_subset_regularizeScheme (A : List ℕ → Set X) :
    suslinOperation A ⊆ suslinOperation (regularizeScheme A) := by
  rintro x ⟨f, hf⟩
  refine ⟨f, fun n => ?_⟩
  intro t ht
  rw [eq_initialSegment_length_of_prefix f ht]
  exact hf t.length

/-- Finite-prefix regularization preserves the Suslin operation exactly.
@isnad1 id=eq.0h2v.s4.f2761ff4aa0b from=translated src=- shape=569a18c8 vocab=42b6bcdd
-/
@[simp]
theorem suslinOperation_regularizeScheme (A : List ℕ → Set X) :
    suslinOperation (regularizeScheme A) = suslinOperation A :=
  Set.Subset.antisymm
    (suslinOperation_regularizeScheme_subset A)
    (suslinOperation_subset_regularizeScheme A)

/-- Regularizing twice has no further effect.
@isnad1 id=eq.0h3v.s4.79dbbf1d8032 from=translated src=- shape=7f351672 vocab=b2a3bab4
-/
@[simp]
theorem regularizeScheme_idem (A : List ℕ → Set X) (s : List ℕ) :
    regularizeScheme (regularizeScheme A) s = regularizeScheme A s :=
  (isRegularSuslinScheme_regularizeScheme A).regularizeScheme_eq s

end DescriptiveSetTheory
