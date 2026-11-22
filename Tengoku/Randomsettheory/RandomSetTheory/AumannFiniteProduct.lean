/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.MeasureTheory.SpecificCodomains.Pi
import Tengoku.Randomsettheory.RandomSetTheory.AumannRealClosedness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectation and finite products

Selections of a finite product correspondence are exactly finite families of
coordinate selections.  Bochner integrability and integration are both
coordinatewise in a finite product, so Aumann expectation commutes exactly
with such products.

Combining this algebraic theorem with real-valued Aumann closedness proves
that every finite product of compact convex real random intervals has a
compact (indeed rectangular) Aumann expectation on an arbitrary measure
space under coordinatewise integrable envelopes.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set

noncomputable section

namespace RandomSetTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Pointwise product of a family of correspondences.-/
def piCorrespondence {E : ι → Type*}
    (S : ∀ i, Ω → Set (E i)) : Ω → Set (∀ i, E i) :=
  fun ω => Set.pi Set.univ fun i => S i ω

omit [MeasurableSpace Ω] in
/--
@isnad1 id=iff.0h6v.s6.743d8ccc0a42 from=translated src=- shape=a2767554 vocab=f64572a4
-/
@[simp]
theorem mem_piCorrespondence {E : ι → Type*}
    {S : ∀ i, Ω → Set (E i)} {ω : Ω} {x : ∀ i, E i} :
    x ∈ piCorrespondence S ω ↔ ∀ i, x i ∈ S i ω := by
  simp [piCorrespondence]

/-- Aumann expectation commutes exactly with finite products.  This requires
no compactness, convexity, or measurable-selection theorem: it is a direct
coordinatewise equivalence between integrable selections.
@isnad1 id=eq.0h5v.s7.05acfa87e1d1 from=translated src=- shape=2d681aa5 vocab=f6ccc131
-/
theorem aumannExpectation_piCorrespondence
    [Fintype ι]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    {μ : Measure Ω} (S : ∀ i, Ω → Set (E i)) :
    aumannExpectation μ (piCorrespondence S) =
      Set.pi Set.univ fun i => aumannExpectation μ (S i) := by
  classical
  ext x
  constructor
  · rintro ⟨f, hf, hfx⟩
    rw [Set.mem_pi]
    intro i _
    refine ⟨fun ω => f ω i, ⟨hf.1.eval i, ?_⟩, ?_⟩
    · filter_upwards [hf.2] with ω hω
      exact (mem_piCorrespondence.mp hω) i
    · calc
        (∫ ω, f ω i ∂μ) = (∫ ω, f ω ∂μ) i :=
          (eval_integral (fun j => hf.1.eval j) i).symm
        _ = x i := congrFun hfx i
  · intro hx
    rw [Set.mem_pi] at hx
    have hcoord : ∀ i, ∃ f : Ω → E i,
        IsIntegrableSelection μ (S i) f ∧ ∫ ω, f ω ∂μ = x i := by
      intro i
      exact hx i (Set.mem_univ i)
    choose f hf hInt using hcoord
    let F : Ω → ∀ i, E i := fun ω i => f i ω
    have hFint : Integrable F μ := by
      apply Integrable.of_eval
      intro i
      exact (hf i).1
    have hFmem : ∀ᵐ ω ∂μ, F ω ∈ piCorrespondence S ω := by
      filter_upwards [Filter.eventually_all.2 fun i => (hf i).2] with ω hω
      rw [mem_piCorrespondence]
      exact hω
    refine ⟨F, ⟨hFint, hFmem⟩, ?_⟩
    funext i
    calc
      (∫ ω, F ω ∂μ) i = ∫ ω, F ω i ∂μ :=
        eval_integral (fun j => hFint.eval j) i
      _ = ∫ ω, f i ω ∂μ := rfl
      _ = x i := hInt i

/-- A finite product of standard real-valued random intervals has a compact
Aumann expectation in the finite-dimensional product space.
@isnad1 id=iscompac.6h5v.s7.c8bb8fa72a58 from=translated src=- shape=d0c05ef9 vocab=043e037b
-/
theorem aumannExpectation_isCompact_pi_real
    [Fintype ι]
    {μ : Measure Ω} {S : ι → Ω → Set ℝ}
    (hS : ∀ i, RandomSet.IsEffrosMeasurable (S i))
    (hcompact : ∀ i ω, IsCompact (S i ω))
    (hne : ∀ i ω, (S i ω).Nonempty)
    (hconv : ∀ i ω, Convex ℝ (S i ω))
    {g : ι → Ω → ℝ} (hg : ∀ i, Integrable (g i) μ)
    (hdom : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ g i ω) :
    IsCompact (aumannExpectation μ (piCorrespondence S)) := by
  rw [aumannExpectation_piCorrespondence]
  exact isCompact_univ_pi fun i =>
    aumannExpectation_isCompact_real (hS i) (hcompact i) (hne i)
      (hconv i) (hg i) (hdom i)

/-- Hence finite products of real random intervals have closed Aumann
expectations before taking a closure.
@isnad1 id=isclosed.6h5v.s7.ca3d8752782a from=translated src=- shape=a798eb52 vocab=819cc819
-/
theorem aumannExpectation_isClosed_pi_real
    [Fintype ι]
    {μ : Measure Ω} {S : ι → Ω → Set ℝ}
    (hS : ∀ i, RandomSet.IsEffrosMeasurable (S i))
    (hcompact : ∀ i ω, IsCompact (S i ω))
    (hne : ∀ i ω, (S i ω).Nonempty)
    (hconv : ∀ i ω, Convex ℝ (S i ω))
    {g : ι → Ω → ℝ} (hg : ∀ i, Integrable (g i) μ)
    (hdom : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ g i ω) :
    IsClosed (aumannExpectation μ (piCorrespondence S)) :=
  (aumannExpectation_isCompact_pi_real hS hcompact hne hconv hg hdom).isClosed

/-- Coordinatewise endpoint selections identify the Aumann expectation of a
finite product as one closed order interval (an axis-aligned rectangle).
@isnad1 id=ex.6h5v.s8.753b3dc9e591 from=translated src=- shape=50401c98 vocab=e78c01ba
-/
theorem exists_Icc_eq_aumannExpectation_pi_real
    [Fintype ι]
    {μ : Measure Ω} {S : ι → Ω → Set ℝ}
    (hS : ∀ i, RandomSet.IsEffrosMeasurable (S i))
    (hcompact : ∀ i ω, IsCompact (S i ω))
    (hne : ∀ i ω, (S i ω).Nonempty)
    (hconv : ∀ i ω, Convex ℝ (S i ω))
    {g : ι → Ω → ℝ} (hg : ∀ i, Integrable (g i) μ)
    (hdom : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ g i ω) :
    ∃ a b : ι → ℝ, a ≤ b ∧
      aumannExpectation μ (piCorrespondence S) = Icc a b := by
  have hi : ∀ i, ∃ a b : ℝ, a ≤ b ∧
      aumannExpectation μ (S i) = Icc a b := by
    intro i
    exact exists_Icc_eq_aumannExpectation_real
      (hS i) (hcompact i) (hne i) (hconv i) (hg i) (hdom i)
  choose a b hab hEq using hi
  refine ⟨a, b, hab, ?_⟩
  rw [aumannExpectation_piCorrespondence]
  simp_rw [hEq]
  exact Set.pi_univ_Icc (x := a) (y := b)

/-- Closure is redundant for finite products of real random intervals.
@isnad1 id=eq.6h5v.s8.0aec56b0fd0b from=translated src=- shape=e46350d8 vocab=3ad678b0
-/
theorem closure_aumannExpectation_eq_pi_real
    [Fintype ι]
    {μ : Measure Ω} {S : ι → Ω → Set ℝ}
    (hS : ∀ i, RandomSet.IsEffrosMeasurable (S i))
    (hcompact : ∀ i ω, IsCompact (S i ω))
    (hne : ∀ i ω, (S i ω).Nonempty)
    (hconv : ∀ i ω, Convex ℝ (S i ω))
    {g : ι → Ω → ℝ} (hg : ∀ i, Integrable (g i) μ)
    (hdom : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ g i ω) :
    closure (aumannExpectation μ (piCorrespondence S)) =
      aumannExpectation μ (piCorrespondence S) :=
  (aumannExpectation_isClosed_pi_real hS hcompact hne hconv hg hdom).closure_eq

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
