/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AtomlessDivisibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-action purification under exact divisibility

Every exactly divisible probability space can implement a finite lottery by
a measurable partition.  This file turns the abstract partition theorem in
`ExactDivisibility` into vector-valued purification and an exact Aumann
expectation identity.

The generic results are methods of `HasExactDivisibility`.  The historical
theorems on the real Borel line are retained as corollaries, using the CDF
divisibility theorem from `LyapunovAtomless`.

No vector-valued Lyapunov theorem is used: finite purification requires only
exact scalar divisibility.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RandomSetTheory

/-! ## Real-line compatibility wrapper for finite partitions -/

/-- Exact finite measurable partition on the real Borel line.  This retains
the original API while delegating to the abstract divisibility theorem.-/
theorem exists_isMeasurableFinpartition_measureReal_eq
    {ι : Type*} (mu : Measure ℝ)
    [IsFiniteMeasure mu] [NullSingletonClass mu]
    (s : Finset ι) (B : Set ℝ) (hB : MeasurableSet B)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) :
    ∃ A : ι → Set ℝ, IsMeasurableFinpartition s B A ∧
      ∀ i ∈ s, mu.real (A i) = w i * mu.real B := by
  exact (hasExactDivisibility_real_of_nullSingletonClass mu)
    |>.exists_isMeasurableFinpartition_measureReal_eq s B hB w hw hsum

/-! ## Purification of finite action mixtures -/

/-- A finite convex combination of actions is realized exactly by a
measurable pure action on any exactly divisible probability space.-/
theorem HasExactDivisibility.exists_integrable_finsetSelection_integral_eq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (hmu : HasExactDivisibility mu)
    (K : Finset E) (w : E → ℝ)
    (hw : ∀ x ∈ K, 0 ≤ w x) (hsum : ∑ x ∈ K, w x = 1) :
    ∃ f : Ω → E, Integrable f mu ∧
      (∀ ω, f ω ∈ (K : Set E)) ∧
      (∫ ω, f ω ∂mu) = ∑ x ∈ K, w x • x := by
  classical
  obtain ⟨A, hApart, hAmeasure⟩ :=
    hmu.exists_isMeasurableFinpartition_measureReal_eq
      K Set.univ MeasurableSet.univ w hw hsum
  rcases hApart with ⟨hAmeas, _hAsub, hAdisj, hAunion⟩
  let f : Ω → E := fun ω ↦
    ∑ x ∈ K, (A x).indicator (fun _ ↦ x) ω
  have hfvalue : ∀ ω, ∃ x ∈ K, f ω = x := by
    intro ω
    have hωUnion : ω ∈ ⋃ x ∈ K, A x := by
      rw [hAunion]
      exact Set.mem_univ ω
    rcases Set.mem_iUnion.mp hωUnion with ⟨x, hωUnion⟩
    rcases Set.mem_iUnion.mp hωUnion with ⟨hxK, hωA⟩
    refine ⟨x, hxK, ?_⟩
    dsimp only [f]
    rw [Finset.sum_eq_single x]
    · exact Set.indicator_of_mem hωA (fun _ ↦ x)
    · intro y hyK hyx
      have hdisj : Disjoint (A y) (A x) :=
        hAdisj y hyK x hxK hyx
      have hωnot : ω ∉ A y := fun hωy ↦
        Set.disjoint_left.mp hdisj hωy hωA
      exact Set.indicator_of_notMem hωnot (fun _ ↦ y)
    · exact fun hx ↦ (hx hxK).elim
  have hfInt : Integrable f mu := by
    dsimp only [f]
    exact integrable_finsetSum K fun x hx ↦
      (integrable_const x).indicator (hAmeas x hx)
  refine ⟨f, hfInt, fun ω ↦ ?_, ?_⟩
  · obtain ⟨x, hxK, hfx⟩ := hfvalue ω
    rw [hfx]
    exact hxK
  · calc
      (∫ ω, f ω ∂mu) =
          ∑ x ∈ K, ∫ ω, (A x).indicator (fun _ ↦ x) ω ∂mu := by
        dsimp only [f]
        exact integral_finsetSum K fun x hx ↦
          (integrable_const x).indicator (hAmeas x hx)
      _ = ∑ x ∈ K, mu.real (A x) • x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact integral_indicator_const x (hAmeas x hx)
      _ = ∑ x ∈ K, w x • x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hAmeasure x hx, probReal_univ, mul_one]

/-- Real-line specialization of finite-action purification.-/
theorem exists_integrable_finsetSelection_integral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (K : Finset E) (w : E → ℝ)
    (hw : ∀ x ∈ K, 0 ≤ w x) (hsum : ∑ x ∈ K, w x = 1) :
    ∃ f : ℝ → E, Integrable f mu ∧
      (∀ ω, f ω ∈ (K : Set E)) ∧
      (∫ ω, f ω ∂mu) = ∑ x ∈ K, w x • x := by
  exact (hasExactDivisibility_real_of_nullSingletonClass mu)
    |>.exists_integrable_finsetSelection_integral_eq mu K w hw hsum

/-- **Finite-action purification theorem.** On any exactly divisible
probability space, the Aumann expectation of a constant finite, possibly
nonconvex, action set is exactly its convex hull.-/
theorem aumannExpectation_const_finset_eq_convexHull_of_exactDivisibility
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (hmu : HasExactDivisibility mu) (K : Finset E) :
    aumannExpectation mu (fun _ ↦ (K : Set E)) =
      convexHull ℝ (K : Set E) := by
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf, rfl⟩
    apply (convex_convexHull ℝ (K : Set E)).integral_mem
      (K.finite_toSet.isClosed_convexHull ℝ) _ hf.1
    filter_upwards [hf.2] with ω hω
    exact subset_convexHull ℝ (K : Set E) hω
  · intro x hx
    obtain ⟨w, hw, hsum, hweighted⟩ :=
      (Finset.mem_convexHull' (R := ℝ)).mp hx
    obtain ⟨f, hfInt, hfK, hfIntegral⟩ :=
      hmu.exists_integrable_finsetSelection_integral_eq mu K w hw hsum
    refine ⟨f, ⟨hfInt, Filter.Eventually.of_forall hfK⟩, ?_⟩
    exact hfIntegral.trans hweighted

/-- Real-line compatibility form of finite-action purification.-/
theorem aumannExpectation_const_finset_eq_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (K : Finset E) :
    aumannExpectation mu (fun _ ↦ (K : Set E)) =
      convexHull ℝ (K : Set E) := by
  exact aumannExpectation_const_finset_eq_convexHull_of_exactDivisibility
    mu (hasExactDivisibility_real_of_nullSingletonClass mu) K

/-- Finite-action purification on every finite atomless probability space,
with no standard-Borel hypothesis on the measurable base.-/
theorem aumannExpectation_const_finset_eq_convexHull_of_atomless
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu) (K : Finset E) :
    aumannExpectation mu (fun _ ↦ (K : Set E)) =
      convexHull ℝ (K : Set E) := by
  exact aumannExpectation_const_finset_eq_convexHull_of_exactDivisibility
    mu (hasExactDivisibility_of_atomless hmu) K

/-- Compatibility specialization of finite-action purification when the
measurable base is explicitly equivalent to the real Borel line.-/
theorem aumannExpectation_const_finset_eq_convexHull_of_atomless_measurableEquiv_real
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu) (_e : Ω ≃ᵐ ℝ) (K : Finset E) :
    aumannExpectation mu (fun _ ↦ (K : Set E)) =
      convexHull ℝ (K : Set E) := by
  exact aumannExpectation_const_finset_eq_convexHull_of_atomless mu hmu K

end RandomSetTheory
