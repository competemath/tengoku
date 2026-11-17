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

/-- Membership in the regularization is membership in every finite-prefix value.-/
@[simp]
theorem mem_regularizeScheme {A : List ℕ → Set X} {s : List ℕ} {x : X} :
    x ∈ regularizeScheme A s ↔ ∀ ⦃t : List ℕ⦄, t <+: s → x ∈ A t :=
  Iff.rfl

/-- Regularization is pointwise contained in the original scheme.-/
theorem regularizeScheme_subset (A : List ℕ → Set X) (s : List ℕ) :
    regularizeScheme A s ⊆ A s := by
  intro x hx
  exact hx (List.prefix_refl s)

/-- Prefix intersections form a regular scheme.-/
theorem isRegularSuslinScheme_regularizeScheme (A : List ℕ → Set X) :
    IsRegularSuslinScheme (regularizeScheme A) := by
  intro s t hst x hx u hus
  exact hx (hus.trans hst)

/-- Regularization is monotone in the underlying scheme.-/
theorem regularizeScheme_mono {A B : List ℕ → Set X} (h : ∀ s, A s ⊆ B s) (s : List ℕ) :
    regularizeScheme A s ⊆ regularizeScheme B s := by
  intro x hx t hts
  exact h t (hx hts)

/-- A regular scheme is unchanged at every node by regularization.-/
theorem IsRegularSuslinScheme.regularizeScheme_eq {A : List ℕ → Set X}
    (hA : IsRegularSuslinScheme A) (s : List ℕ) : regularizeScheme A s = A s := by
  apply Set.Subset.antisymm (regularizeScheme_subset A s)
  intro x hx t hts
  exact hA hts hx

/-- Constant schemes are fixed by regularization.-/
@[simp]
theorem regularizeScheme_const (S : Set X) (s : List ℕ) :
    regularizeScheme (fun _ => S) s = S := by
  apply Set.Subset.antisymm
  · exact regularizeScheme_subset _ s
  · intro x hx t _
    exact hx

/-- The Suslin operation of the regularization is contained in the original operation.-/
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

/-- Every original Suslin witness is also a witness for the regularized scheme.-/
theorem suslinOperation_subset_regularizeScheme (A : List ℕ → Set X) :
    suslinOperation A ⊆ suslinOperation (regularizeScheme A) := by
  rintro x ⟨f, hf⟩
  refine ⟨f, fun n => ?_⟩
  intro t ht
  rw [eq_initialSegment_length_of_prefix f ht]
  exact hf t.length

/-- Finite-prefix regularization preserves the Suslin operation exactly.-/
@[simp]
theorem suslinOperation_regularizeScheme (A : List ℕ → Set X) :
    suslinOperation (regularizeScheme A) = suslinOperation A :=
  Set.Subset.antisymm
    (suslinOperation_regularizeScheme_subset A)
    (suslinOperation_subset_regularizeScheme A)

/-- Regularizing twice has no further effect.-/
@[simp]
theorem regularizeScheme_idem (A : List ℕ → Set X) (s : List ℕ) :
    regularizeScheme (regularizeScheme A) s = regularizeScheme A s :=
  (isRegularSuslinScheme_regularizeScheme A).regularizeScheme_eq s

end DescriptiveSetTheory
