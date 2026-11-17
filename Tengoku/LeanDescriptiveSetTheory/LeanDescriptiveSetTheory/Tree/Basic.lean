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

/--
@isnad1 id=eq.0h2v.s4.3020c10c1cfc from=translated src=- shape=fbd3ea0c vocab=2ba4c362
-/
@[simp]
theorem initialSegment_zero (x : ℕ → A) : initialSegment x 0 = [] := by
  rfl

/--
@isnad1 id=eq.0h3v.s4.40c765deb0be from=translated src=- shape=087d1dfe vocab=648f0117
-/
@[simp]
theorem length_initialSegment (x : ℕ → A) (n : ℕ) : (initialSegment x n).length = n := by
  simp [initialSegment]

/-- Passing from length `n` to length `n + 1` appends the next coordinate.
@isnad1 id=eq.0h3v.s5.6fc7526a0fe9 from=translated src=- shape=4ef692dd vocab=604e01c1
-/
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

/--
@isnad1 id=iff.0h3v.s7.a3f434320f8d from=translated src=- shape=67ef6b50 vocab=ad60aaad
-/
@[simp]
theorem mem_body {x : ℕ → A} :
    x ∈ body T ↔ ∀ n, initialSegment x n ∈ T :=
  Iff.rfl

/-- Inclusion of trees induces inclusion of their bodies.
@isnad1 id=le.1h3v.s8.ab6d1f4ded96 from=translated src=- shape=072d0957 vocab=433f69b2
-/
theorem body_mono (h : S ≤ T) : body S ⊆ body T := by
  intro x hx n
  exact h (hx n)

/--
@isnad1 id=eq.0h1v.s6.001045a59868 from=translated src=- shape=5991df13 vocab=3a1d8d8f
-/
@[simp]
theorem body_bot : body (⊥ : Descriptive.tree A) = ∅ := by
  ext x
  simp [body, IsBranch]

/--
@isnad1 id=eq.0h1v.s6.83bf4a951ffe from=translated src=- shape=3a7d51a8 vocab=8f2acd8f
-/
@[simp]
theorem body_top : body (⊤ : Descriptive.tree A) = Set.univ := by
  ext x
  simp [body, IsBranch]

/--
@isnad1 id=eq.0h3v.s7.5b94251d2c3d from=translated src=- shape=18204471 vocab=e6a2e3a7
-/
@[simp]
theorem body_inf (S T : Descriptive.tree A) : body (S ⊓ T) = body S ∩ body T := by
  ext x
  simp [body, IsBranch, forall_and]

/--
@isnad1 id=eq.0h3v.s7.3d50f36ca62a from=translated src=- shape=0807731f vocab=e02dd41d
-/
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

/-- The body of a tree over a discrete alphabet is closed in the product topology.
@isnad1 id=isclosed.0h2v.s6.bcda3e46b5eb from=translated src=- shape=2f47be7a vocab=df4a2bc2
-/
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
