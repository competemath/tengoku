/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Suslin operation

This file defines the classical Suslin operation on a plain family `A : List ℕ → Set X`.
The public convention uses `Tree.initialSegment f n`, so the prefix has length `n` and the empty
prefix participates at `n = 0`. This matches the existing tree-body API exactly.

Only the pure set operation, its membership equation, pointwise monotonicity, and preimage
compatibility are stabilized here. No bundled scheme laws or generic pointclass interface are
introduced.
-/

open Set

universe u v

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

/-- The Suslin operation on a family indexed by finite sequences of natural numbers.

A point belongs when one Baire-space witness places it in every set indexed by the witness's
length-`n` initial segment. In particular, the empty prefix is tested at `n = 0`.-/
def suslinOperation (A : List ℕ → Set X) : Set X :=
  {x | ∃ f : ℕ → ℕ, ∀ n, x ∈ A (initialSegment f n)}

/-- Membership expansion for the Suslin operation.-/
@[simp]
theorem mem_suslinOperation {A : List ℕ → Set X} {x : X} :
    x ∈ suslinOperation A ↔
      ∃ f : ℕ → ℕ, ∀ n, x ∈ A (initialSegment f n) :=
  Iff.rfl

/-- Pointwise inclusion of schemes induces inclusion of their Suslin operations.-/
theorem suslinOperation_mono {A B : List ℕ → Set X} (h : ∀ s, A s ⊆ B s) :
    suslinOperation A ⊆ suslinOperation B := by
  rintro x ⟨f, hf⟩
  exact ⟨f, fun n => h _ (hf n)⟩

/-- Preimages commute with the Suslin operation.-/
@[simp]
theorem preimage_suslinOperation {Y : Type v} (g : Y → X) (A : List ℕ → Set X) :
    g ⁻¹' suslinOperation A = suslinOperation fun s => g ⁻¹' A s := by
  rfl

end DescriptiveSetTheory
