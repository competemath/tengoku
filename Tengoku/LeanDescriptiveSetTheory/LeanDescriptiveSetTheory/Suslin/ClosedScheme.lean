/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Basic
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Suslin operations on closed schemes

For a scheme `A : List ℕ → Set X`, this file packages all prefix constraints as a relation on
Baire witness space times `X`. If every `A s` is closed, the relation is closed: each fixed-length
constraint factors through the finitely many coordinates `Fin n → ℕ`, whose topology is discrete.

The Suslin operation is exactly the second-coordinate image of this relation. Its analyticity
therefore follows from closed-set analyticity and continuous projection, not from closure under an
uncountable union.
-/

open Set

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

/-- The relation whose points satisfy every finite-prefix constraint of a scheme.-/
def closedSchemeRelation (A : List ℕ → Set X) : Set ((ℕ → ℕ) × X) :=
  {p | ∀ n, p.2 ∈ A (initialSegment p.1 n)}

/-- Membership expansion for the relation associated with a scheme.
@isnad1 id=iff.0h3v.s5.7c6210238aa0 from=translated src=- shape=8c44f3f6 vocab=6e35080f
-/
@[simp]
theorem mem_closedSchemeRelation {A : List ℕ → Set X} {p : (ℕ → ℕ) × X} :
    p ∈ closedSchemeRelation A ↔
      ∀ n, p.2 ∈ A (initialSegment p.1 n) :=
  Iff.rfl

/-- The Suslin operation is the second-coordinate projection of its associated relation.
@isnad1 id=eq.0h2v.s4.028f4124a462 from=translated src=- shape=8874a589 vocab=cb68cba8
-/
theorem suslinOperation_eq_snd_image_closedSchemeRelation (A : List ℕ → Set X) :
    suslinOperation A = Prod.snd '' closedSchemeRelation A := by
  ext x
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨(f, x), hf, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp⟩

section Topology

variable [TopologicalSpace X]

private theorem isClosed_closedSchemeConstraint (A : List ℕ → Set X)
    (hA : ∀ s, IsClosed (A s)) (n : ℕ) :
    IsClosed {p : (ℕ → ℕ) × X | p.2 ∈ A (initialSegment p.1 n)} := by
  let R : Set ((Fin n → ℕ) × X) :=
    {q | q.2 ∈ A (List.ofFn q.1)}
  have hR : IsClosed R := by
    rw [← isOpen_compl_iff]
    have hcompl :
        Rᶜ = ⋃ s : Fin n → ℕ,
          ({s} : Set (Fin n → ℕ)) ×ˢ (A (List.ofFn s))ᶜ := by
      ext q
      simp [R]
    rw [hcompl]
    exact isOpen_iUnion fun s =>
      (isOpen_discrete {s}).prod (hA _).isOpen_compl
  have hfirst : Continuous (fun p : (ℕ → ℕ) × X =>
      fun i : Fin n => p.1 (i : ℕ)) :=
    continuous_pi fun i =>
      (continuous_apply (i : ℕ)).comp continuous_fst
  have hcontinuous : Continuous (fun p : (ℕ → ℕ) × X =>
      ((fun i : Fin n => p.1 i), p.2)) :=
    hfirst.prodMk continuous_snd
  simpa [R, initialSegment] using hR.preimage hcontinuous

/-- If every set in a scheme is closed, its associated prefix relation is closed.
@isnad1 id=isclosed.1h2v.s5.c4493b402bcc from=translated src=- shape=ccd75262 vocab=50a63d0a
-/
theorem isClosed_closedSchemeRelation (A : List ℕ → Set X)
    (hA : ∀ s, IsClosed (A s)) :
    IsClosed (closedSchemeRelation A) := by
  rw [show closedSchemeRelation A = ⋂ n,
      {p : (ℕ → ℕ) × X | p.2 ∈ A (initialSegment p.1 n)} by
    ext p
    simp [closedSchemeRelation]]
  exact isClosed_iInter (isClosed_closedSchemeConstraint A hA)

/-- The Suslin operation applied to a closed scheme in a Polish space is analytic.
@isnad1 id=analytic.1h2v.s4.6f34e4361f3d from=translated src=- shape=68a225f3 vocab=020c0c11
-/
theorem analyticSet_suslinOperation_of_isClosed [PolishSpace X]
    (A : List ℕ → Set X) (hA : ∀ s, IsClosed (A s)) :
    MeasureTheory.AnalyticSet (suslinOperation A) := by
  rw [suslinOperation_eq_snd_image_closedSchemeRelation]
  exact (isClosed_closedSchemeRelation A hA).analyticSet.image_of_continuous
    continuous_snd

end Topology

end DescriptiveSetTheory
