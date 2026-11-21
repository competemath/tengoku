/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SupportSelection
import Tengoku.Randomsettheory.RandomSetTheory.Geometry
import Tengoku.Randomsettheory.RandomSetTheory.EffrosConvexHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Convexification of Aumann expectations

This file proves the closed convexification identity that does not require
atomlessness.  It cleanly isolates the remaining purification step: an
atomless Lyapunov theorem is needed only to remove the closed convex hulls.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- An envelope valid on a set is still valid on its closed convex hull.-/
theorem norm_le_on_closedConvexHull_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    ∀ x ∈ closedConvexHull ℝ K, ‖x‖ ≤ R := by
  intro x hx
  have hsub : K ⊆ Metric.closedBall (0 : E) R := by
    intro y hy
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR y hy
  have hxball : x ∈ Metric.closedBall (0 : E) R :=
    closedConvexHull_min hsub (convex_closedBall (0 : E) R)
      Metric.isClosed_closedBall hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using hxball

/-- Closed convexification commutes with the closed Aumann expectation.

Unlike the stronger purification identity, this theorem needs no atomless
measure.  Effros measurability of the pointwise closed convex hull is kept as
an explicit hypothesis until a general convex-hull measurability theorem is
available in the library.-/
theorem closedConvexHull_closure_aumannExpectation_eq
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → Set H}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hHull : RandomSet.IsEffrosMeasurable
      (fun ω => closedConvexHull ℝ (S ω)))
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    closedConvexHull ℝ (closure (aumannExpectation μ S)) =
      closure (aumannExpectation μ
        (fun ω => closedConvexHull ℝ (S ω))) := by
  let C : Ω → Set H := fun ω => closedConvexHull ℝ (S ω)
  have hCcompact : ∀ ω, IsCompact (C ω) := fun ω =>
    closedConvexHull_compact (hcompact ω)
  have hCne : ∀ ω, (C ω).Nonempty := fun ω =>
    (hne ω).mono subset_closedConvexHull
  have hCdom : ∀ ω, ∀ x ∈ C ω, ‖x‖ ≤ g ω := fun ω =>
    norm_le_on_closedConvexHull_of_norm_le (hdom ω)
  have hAcompact : IsCompact (closure (aumannExpectation μ S)) :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hdom)
  have hCcompactA : IsCompact (closure (aumannExpectation μ C)) :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hCdom)
  have hfS : IsIntegrableSelection μ S
      (supportApproximateSelection hS hcompact hne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS hcompact hne hg hdom 0 (by norm_num)
  have hfC : IsIntegrableSelection μ C
      (supportApproximateSelection hHull hCcompact hCne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hHull hCcompact hCne hg hCdom 0 (by norm_num)
  have hAne : (closure (aumannExpectation μ S)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfS).closure
  have hCAne : (closure (aumannExpectation μ C)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfC).closure
  have hCAconv : Convex ℝ (closure (aumannExpectation μ C)) :=
    (aumannExpectation_convex
      (Filter.Eventually.of_forall fun ω => convex_closedConvexHull)).closure
  apply eq_of_supportFunction_eq
    (closedConvexHull_compact hAcompact) hCcompactA
    (hAne.mono subset_closedConvexHull) hCAne
    convex_closedConvexHull hCAconv
  intro u
  rw [supportFunction_closedConvexHull hAcompact hAne u]
  rw [supportFunction_closure_aumannExpectation_of_envelope
    hS hcompact hne hg hdom hAcompact u]
  rw [supportFunction_closure_aumannExpectation_of_envelope
    hHull hCcompact hCne hg hCdom hCcompactA u]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact (supportFunction_closedConvexHull (hcompact ω) (hne ω) u).symm

/-- Conditional purification identity.  Lyapunov convexity removes the
outer convex hull in the preceding theorem; closedness of the two Aumann
expectations removes their closures.  Thus the only missing ingredient for
the usual atomless statement is the genuine atomless Lyapunov theorem and
the standard Aumann closedness theorem.-/
theorem aumannExpectation_closedConvexHull_eq_of_lyapunov
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → Set H}
    (hμ : HasLyapunovConvexity μ H)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hHull : RandomSet.IsEffrosMeasurable
      (fun ω => closedConvexHull ℝ (S ω)))
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hASclosed : IsClosed (aumannExpectation μ S))
    (hACclosed : IsClosed (aumannExpectation μ
      (fun ω => closedConvexHull ℝ (S ω)))) :
    aumannExpectation μ S =
      aumannExpectation μ
        (fun ω => closedConvexHull ℝ (S ω)) := by
  have hEq := closedConvexHull_closure_aumannExpectation_eq
    hS hHull hcompact hne hg hdom
  rw [hASclosed.closure_eq, hACclosed.closure_eq] at hEq
  have hconv : Convex ℝ (aumannExpectation μ S) :=
    aumannExpectation_convex_of_lyapunov hμ S
  have hhull : closedConvexHull ℝ (aumannExpectation μ S) =
      aumannExpectation μ S := by
    apply Set.Subset.antisymm
    · exact closedConvexHull_min Subset.rfl hconv hASclosed
    · exact subset_closedConvexHull
  rwa [hhull] at hEq

/-- Automatic Effros version of
`closedConvexHull_closure_aumannExpectation_eq`.  Measurability of the
pointwise closed convex hull is derived from the compact nonempty fibres.-/
theorem closedConvexHull_closure_aumannExpectation_eq_of_effros
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → Set H}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    closedConvexHull ℝ (closure (aumannExpectation μ S)) =
      closure (aumannExpectation μ
        (fun ω => closedConvexHull ℝ (S ω))) := by
  exact closedConvexHull_closure_aumannExpectation_eq
    hS (effrosMeasurable_closedConvexHull_of_compact hS hcompact hne)
    hcompact hne hg hdom

/-- Automatic Effros form of the conditional purification theorem.  The
only remaining non-constructive mathematical inputs are genuine Lyapunov
convexity and closedness of the two Aumann expectations.-/
theorem aumannExpectation_closedConvexHull_eq_of_lyapunov_of_effros
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → Set H}
    (hμ : HasLyapunovConvexity μ H)
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hASclosed : IsClosed (aumannExpectation μ S))
    (hACclosed : IsClosed (aumannExpectation μ
      (fun ω => closedConvexHull ℝ (S ω)))) :
    aumannExpectation μ S =
      aumannExpectation μ
        (fun ω => closedConvexHull ℝ (S ω)) := by
  exact aumannExpectation_closedConvexHull_eq_of_lyapunov
    hμ hS (effrosMeasurable_closedConvexHull_of_compact hS hcompact hne)
    hcompact hne hg hdom hASclosed hACclosed

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
