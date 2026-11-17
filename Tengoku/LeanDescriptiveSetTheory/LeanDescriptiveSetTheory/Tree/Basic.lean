/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.Data.List.OfFn
import Tengoku.Seed.SetTheory.Descriptive.Tree
import Tengoku.Seed.Topology.Clopen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Branches and bodies of descriptive-set-theoretic trees

Mathlib's `Descriptive.tree A` is a prefix-closed set of finite lists over `A`. This file adds the
standard infinite objects associated with such a tree: the finite initial segment of a sequence,
the predicate that a sequence is a branch, and the body consisting of all branches.

For a discrete alphabet, the body is closed in the product topology. The proof factors every
length-`n` condition through the finite discrete space `Fin n → A`, so no topology is imposed on
the list type itself.
-/

open Set

universe u

namespace DescriptiveSetTheory.Tree

variable {A : Type u} {S T : Descriptive.tree A}

/-- The list of the first `n` values of an infinite sequence.-/
def initialSegment (x : ℕ → A) (n : ℕ) : List A :=
  List.ofFn fun i : Fin n => x i

@[simp]
theorem initialSegment_zero (x : ℕ → A) : initialSegment x 0 = [] := by
  rfl

@[simp]
theorem length_initialSegment (x : ℕ → A) (n : ℕ) : (initialSegment x n).length = n := by
  simp [initialSegment]

/-- Passing from length `n` to length `n + 1` appends the next coordinate.-/
theorem initialSegment_succ (x : ℕ → A) (n : ℕ) :
    initialSegment x (n + 1) = initialSegment x n ++ [x n] := by
  simpa [initialSegment] using
    (List.ofFn_succ' (fun i : Fin (n + 1) => x i))

/-- An infinite sequence is a branch when every finite initial segment belongs to the tree.-/
def IsBranch (T : Descriptive.tree A) (x : ℕ → A) : Prop :=
  ∀ n, initialSegment x n ∈ T

/-- The body of a tree is the set of all its infinite branches.-/
def body (T : Descriptive.tree A) : Set (ℕ → A) :=
  {x | IsBranch T x}

@[simp]
theorem mem_body {x : ℕ → A} :
    x ∈ body T ↔ ∀ n, initialSegment x n ∈ T :=
  Iff.rfl

/-- Inclusion of trees induces inclusion of their bodies.-/
theorem body_mono (h : S ≤ T) : body S ⊆ body T := by
  intro x hx n
  exact h (hx n)

@[simp]
theorem body_bot : body (⊥ : Descriptive.tree A) = ∅ := by
  ext x
  simp [body, IsBranch]

@[simp]
theorem body_top : body (⊤ : Descriptive.tree A) = Set.univ := by
  ext x
  simp [body, IsBranch]

@[simp]
theorem body_inf (S T : Descriptive.tree A) : body (S ⊓ T) = body S ∩ body T := by
  ext x
  simp [body, IsBranch, forall_and]

@[simp]
theorem body_iInf {ι : Sort*} (T : ι → Descriptive.tree A) :
    body (⨅ i, T i) = ⋂ i, body (T i) := by
  ext x
  simp only [mem_body, CompleteSublattice.mem_iInf, Set.mem_iInter]
  constructor
  · intro hx i n
    exact hx n i
  · intro hx n i
    exact hx i n

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

/-- The body of a tree over a discrete alphabet is closed in the product topology.-/
theorem isClosed_body (T : Descriptive.tree A) : IsClosed (body T) := by
  rw [show body T = ⋂ n, (fun x : ℕ → A => fun i : Fin n => x i) ⁻¹'
      {f : Fin n → A | List.ofFn f ∈ T} by
    ext x
    simp [body, IsBranch, initialSegment]]
  exact isClosed_iInter fun n =>
    (isClopen_discrete {f : Fin n → A | List.ofFn f ∈ T}).isClosed.preimage
      (show Continuous (fun x : ℕ → A => fun i : Fin n => x i) from
        continuous_pi fun i => continuous_apply (i : ℕ))

end Topology

end DescriptiveSetTheory.Tree
