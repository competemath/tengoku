/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Normalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic-valued Suslin schemes

If every component of a Suslin scheme on a Polish space is analytic, then its Suslin operation is
analytic. For a fixed level, branch membership is a countable union over finite prefixes of the
intersection of a closed cylinder with the preimage of one analytic component. The full branch
relation is the countable intersection of these level constraints, and its second-coordinate image
is the Suslin operation.

The final proof first applies finite-prefix regularization from `Suslin.Regular`. This exposes a
regular analytic-valued scheme while `suslinOperation_regularizeScheme` removes regularity from the
public assumptions. No component is silently strengthened from analytic to closed.
-/

open Set

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

/-- The branch/object relation associated with a Suslin scheme. The first coordinate is the Baire
witness and the second is the object retained by the Suslin operation.-/
def analyticSchemeRelation (A : List ℕ → Set X) : Set ((ℕ → ℕ) × X) :=
  closedSchemeRelation A

/-- Membership in the branch/object relation is membership in every component along the branch.
@isnad1 id=iff.0h3v.s5.d1856e3ddacc from=translated src=- shape=8c44f3f6 vocab=3ab37094
-/
@[simp]
theorem mem_analyticSchemeRelation {A : List ℕ → Set X} {p : (ℕ → ℕ) × X} :
    p ∈ analyticSchemeRelation A ↔
      ∀ n, p.2 ∈ A (initialSegment p.1 n) :=
  Iff.rfl

/-- The single-level constraint used to assemble the analytic branch relation.-/
def analyticSchemeConstraint (A : List ℕ → Set X) (n : ℕ) :
    Set ((ℕ → ℕ) × X) :=
  {p | p.2 ∈ A (initialSegment p.1 n)}

/-- Projecting the branch/object relation onto objects gives exactly the Suslin operation.
@isnad1 id=eq.0h2v.s4.0375f52e5722 from=translated src=- shape=8874a589 vocab=a512c71a
-/
theorem suslinOperation_eq_snd_image_analyticSchemeRelation (A : List ℕ → Set X) :
    suslinOperation A = Prod.snd '' analyticSchemeRelation A :=
  suslinOperation_eq_snd_image_closedSchemeRelation A

section Topology

variable [TopologicalSpace X] [PolishSpace X]

private theorem AnalyticSet.inter {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {s t : Set Y} (hs : MeasureTheory.AnalyticSet s)
    (ht : MeasureTheory.AnalyticSet t) : MeasureTheory.AnalyticSet (s ∩ t) := by
  let f : Bool → Set Y := fun b => if b then s else t
  have hf : ∀ b, MeasureTheory.AnalyticSet (f b) := by
    intro b
    cases b <;> simp [f, hs, ht]
  rw [show s ∩ t = ⋂ b, f b by
    ext x
    simp [f, and_comm]]
  exact MeasureTheory.AnalyticSet.iInter hf

/-- Each finite-level branch constraint is analytic when every scheme component is analytic.
@isnad1 id=analytic.1h3v.s5.f7284b1b8a1e from=translated src=- shape=7d596b0f vocab=0a15344a
-/
theorem analyticSet_analyticSchemeConstraint (A : List ℕ → Set X)
    (hA : ∀ s, MeasureTheory.AnalyticSet (A s)) (n : ℕ) :
    MeasureTheory.AnalyticSet (analyticSchemeConstraint A n) := by
  rw [show analyticSchemeConstraint A n =
      ⋃ s : Fin n → ℕ,
        {p : (ℕ → ℕ) × X | (fun i : Fin n => p.1 i) = s} ∩
          Prod.snd ⁻¹' A (List.ofFn s) by
    ext p
    simp [analyticSchemeConstraint, initialSegment]]
  exact MeasureTheory.AnalyticSet.iUnion fun s => by
    apply AnalyticSet.inter
    · have hfirst : Continuous (fun p : (ℕ → ℕ) × X =>
          fun i : Fin n => p.1 (i : ℕ)) :=
        continuous_pi fun i =>
          (continuous_apply (i : ℕ)).comp continuous_fst
      exact (isClosed_eq hfirst continuous_const).analyticSet
    · exact (hA (List.ofFn s)).preimage continuous_snd

/-- The complete branch/object relation is analytic for every analytic-valued scheme.
@isnad1 id=analytic.1h2v.s5.2efb8af779b5 from=translated src=- shape=050212a6 vocab=9305eb57
-/
theorem analyticSet_analyticSchemeRelation (A : List ℕ → Set X)
    (hA : ∀ s, MeasureTheory.AnalyticSet (A s)) :
    MeasureTheory.AnalyticSet (analyticSchemeRelation A) := by
  rw [show analyticSchemeRelation A = ⋂ n, analyticSchemeConstraint A n by
    ext p
    simp [analyticSchemeRelation, analyticSchemeConstraint, closedSchemeRelation]]
  exact MeasureTheory.AnalyticSet.iInter fun n =>
    analyticSet_analyticSchemeConstraint A hA n

/-- Finite-prefix regularization preserves analytic-valuedness.
@isnad1 id=analytic.1h3v.s5.6624492c8a75 from=translated src=- shape=73360436 vocab=8a45e512
-/
theorem analyticSet_regularizeScheme (A : List ℕ → Set X)
    (hA : ∀ s, MeasureTheory.AnalyticSet (A s)) (s : List ℕ) :
    MeasureTheory.AnalyticSet (regularizeScheme A s) := by
  let t0 : {t : List ℕ // t <+: s} := ⟨s, List.prefix_refl s⟩
  letI : Nonempty {t : List ℕ // t <+: s} := ⟨t0⟩
  rw [show regularizeScheme A s = ⋂ t : {t : List ℕ // t <+: s}, A t.1 by
    ext x
    simp [regularizeScheme]]
  exact MeasureTheory.AnalyticSet.iInter fun t => hA t.1

/-- The Suslin operation of an analytic-valued scheme on a Polish space is analytic.
@isnad1 id=analytic.1h2v.s4.218c6d58a4f4 from=translated src=- shape=86014219 vocab=4b431caa
-/
theorem analyticSet_suslinOperation_of_analytic (A : List ℕ → Set X)
    (hA : ∀ s, MeasureTheory.AnalyticSet (A s)) :
    MeasureTheory.AnalyticSet (suslinOperation A) := by
  have hregular : ∀ s, MeasureTheory.AnalyticSet (regularizeScheme A s) :=
    analyticSet_regularizeScheme A hA
  have hrelation := analyticSet_analyticSchemeRelation (regularizeScheme A) hregular
  have himage := hrelation.image_of_continuous continuous_snd
  rw [← suslinOperation_eq_snd_image_analyticSchemeRelation,
    suslinOperation_regularizeScheme] at himage
  exact himage

section Borel

variable [MeasurableSpace X] [BorelSpace X]

/-- A Borel-valued scheme is a special case of an analytic-valued scheme.
@isnad1 id=analytic.1h2v.s5.aa25f2a654fb from=translated src=- shape=ef4f0267 vocab=48b272e5
-/
theorem analyticSet_suslinOperation_of_measurable (A : List ℕ → Set X)
    (hA : ∀ s, MeasurableSet (A s)) :
    MeasureTheory.AnalyticSet (suslinOperation A) :=
  analyticSet_suslinOperation_of_analytic A fun s => (hA s).analyticSet

end Borel

end Topology

end DescriptiveSetTheory
