/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableMaximum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closedness of real-valued Aumann expectations

For a compact nonempty Effros-measurable correspondence with convex values
in `ℝ`, an integrable envelope is enough to prove that its Aumann expectation
is a compact interval, without inserting a closure.

The proof does not need weak compactness in `L¹`.  Exact measurable support
maximizers in directions `-1` and `1` give integrable selections realizing
the lower and upper endpoints.  Every other selection lies between them
almost everywhere, while convexity fills the whole interval.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real-valued compact convex random set has an Aumann expectation which
is exactly a nonempty closed interval.-/
theorem exists_Icc_eq_aumannExpectation_real
    {μ : Measure Ω} {S : Ω → Set ℝ}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    (hconv : ∀ ω, Convex ℝ (S ω))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    ∃ a b : ℝ, a ≤ b ∧ aumannExpectation μ S = Icc a b := by
  obtain ⟨fmin, hfmin, hmin⟩ :=
    hasIntegrableSupportSelection_of_effros_of_envelope
      hS hcompact hne hg hdom (-1 : ℝ)
  obtain ⟨fmax, hfmax, hmax⟩ :=
    hasIntegrableSupportSelection_of_effros_of_envelope
      hS hcompact hne hg hdom (1 : ℝ)
  let a : ℝ := ∫ ω, fmin ω ∂μ
  let b : ℝ := ∫ ω, fmax ω ∂μ
  have hmin_le_max : fmin ≤ᵐ[μ] fmax := by
    filter_upwards [hfmin.2, hfmax.2, hmax] with ω hfminω hfmaxω hmaxω
    have hle := inner_le_supportFunction (hcompact ω) hfminω (1 : ℝ)
    rw [← hmaxω] at hle
    simpa using hle
  have hab : a ≤ b := by
    exact integral_mono_ae hfmin.1 hfmax.1 hmin_le_max
  have ha : a ∈ aumannExpectation μ S :=
    ⟨fmin, hfmin, rfl⟩
  have hb : b ∈ aumannExpectation μ S :=
    ⟨fmax, hfmax, rfl⟩
  have hAconv : Convex ℝ (aumannExpectation μ S) :=
    aumannExpectation_convex (Filter.Eventually.of_forall hconv)
  refine ⟨a, b, hab, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨f, hf, rfl⟩
    constructor
    · apply integral_mono_ae hfmin.1 hf.1
      filter_upwards [hfmin.2, hf.2, hmin] with ω hfminω hfω hminω
      have hle := inner_le_supportFunction (hcompact ω) hfω (-1 : ℝ)
      rw [← hminω] at hle
      simpa using hle
    · apply integral_mono_ae hf.1 hfmax.1
      filter_upwards [hf.2, hfmax.2, hmax] with ω hfω hfmaxω hmaxω
      have hle := inner_le_supportFunction (hcompact ω) hfω (1 : ℝ)
      rw [← hmaxω] at hle
      simpa using hle
  · exact hAconv.ordConnected.out ha hb

/-- General compactness, before closure, for real-valued compact convex
Effros correspondences with an integrable envelope.-/
theorem aumannExpectation_isCompact_real
    {μ : Measure Ω} {S : Ω → Set ℝ}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    (hconv : ∀ ω, Convex ℝ (S ω))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    IsCompact (aumannExpectation μ S) := by
  obtain ⟨a, b, _, hEq⟩ :=
    exists_Icc_eq_aumannExpectation_real hS hcompact hne hconv hg hdom
  rw [hEq]
  exact isCompact_Icc

/-- Real-valued Aumann expectations under the standard hypotheses are
closed without a `closure` wrapper.-/
theorem aumannExpectation_isClosed_real
    {μ : Measure Ω} {S : Ω → Set ℝ}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    (hconv : ∀ ω, Convex ℝ (S ω))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    IsClosed (aumannExpectation μ S) :=
  (aumannExpectation_isCompact_real hS hcompact hne hconv hg hdom).isClosed

/-- The closure used by the ambient finite-dimensional theory disappears
entirely in the real-valued convex case.-/
theorem closure_aumannExpectation_eq_real
    {μ : Measure Ω} {S : Ω → Set ℝ}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    (hconv : ∀ ω, Convex ℝ (S ω))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    closure (aumannExpectation μ S) = aumannExpectation μ S :=
  (aumannExpectation_isClosed_real hS hcompact hne hconv hg hdom).closure_eq

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
