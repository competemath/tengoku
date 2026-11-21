/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Basic
import Tengoku.Randomsettheory.RandomSetTheory.SupportFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of support functions

Effros measurability is precisely what is needed to make the supremum of a
continuous functional over compact nonempty values measurable.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- The support function of an Effros-measurable compact nonempty
correspondence is measurable in every fixed direction.-/
theorem measurable_supportFunction
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : E) :
    Measurable (fun ω => supportFunction (S ω) u) := by
  apply measurable_of_Ioi
  intro a
  have hEq : (fun ω => supportFunction (S ω) u) ⁻¹' Ioi a =
      {ω | (S ω ∩ {x : E | a < ⟪u, x⟫_ℝ}).Nonempty} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
    constructor
    · intro hsup
      obtain ⟨x, hx, hxEq⟩ := supportFunction_attains (hcompact ω) (hne ω) u
      exact ⟨x, hx, by simpa [← hxEq] using hsup⟩
    · rintro ⟨x, hx, hax⟩
      exact hax.trans_le (inner_le_supportFunction (hcompact ω) hx u)
  rw [hEq]
  apply hS
  exact isOpen_lt continuous_const (by fun_prop)

/-- An integrable envelope for the values makes every directional support
function integrable.-/
theorem integrable_supportFunction_of_envelope
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → ℝ}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (hg : Integrable g μ) (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (u : E) :
    Integrable (fun ω => supportFunction (S ω) u) μ := by
  apply (hg.const_mul ‖u‖).mono'
    (measurable_supportFunction hS hcompact hne u).aestronglyMeasurable
  filter_upwards [] with ω
  obtain ⟨x, hx, hxEq⟩ := supportFunction_attains (hcompact ω) (hne ω) u
  rw [hxEq, Real.norm_eq_abs]
  calc
    |⟪u, x⟫_ℝ| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * g ω :=
      mul_le_mul_of_nonneg_left (hdom ω x hx) (norm_nonneg u)

/-- Wrapper for an Effros random closed set with compact nonempty values.-/
theorem RandomSet.EffrosRandomClosedSet.measurable_supportFunction
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : RandomSet.EffrosRandomClosedSet Ω E)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : E) :
    Measurable (fun ω => supportFunction (S ω) u) :=
  RandomSetTheory.measurable_supportFunction S.measurable' hcompact hne u

theorem RandomSet.EffrosRandomClosedSet.integrable_supportFunction_of_envelope
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} (S : RandomSet.EffrosRandomClosedSet Ω E)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) (u : E) :
    Integrable (fun ω => supportFunction (S ω) u) μ :=
  RandomSetTheory.integrable_supportFunction_of_envelope
    S.measurable' hcompact hne hg hdom u

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
