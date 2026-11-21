/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SupportSelection
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableMaximum
import Tengoku.Randomsettheory.RandomSetTheory.Geometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hausdorff stability of the Aumann expectation

The support-function identity and the support/Hausdorff duality imply that
the Aumann expectation is nonexpansive from the integrated pointwise
Hausdorff distance to Hausdorff distance.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory Filter
open scoped Pointwise InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Hausdorff stability of Aumann expectation.  The support-selection
hypotheses are exactly the measurable maximum theorem needed to invoke the
sharp support identity in every direction.-/
theorem hausdorffDist_aumannExpectation_le_integral
    {μ : Measure Ω} {S T : Ω → Set E}
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    (hSconv : ∀ ω, Convex ℝ (S ω))
    (hTconv : ∀ ω, Convex ℝ (T ω))
    (hAScompact : IsCompact (aumannExpectation μ S))
    (hATcompact : IsCompact (aumannExpectation μ T))
    (hASne : (aumannExpectation μ S).Nonempty)
    (hATne : (aumannExpectation μ T).Nonempty)
    (hSupportS : ∀ u, Integrable (fun ω => supportFunction (S ω) u) μ)
    (hSupportT : ∀ u, Integrable (fun ω => supportFunction (T ω) u) μ)
    (hSelectionS : ∀ u, HasIntegrableSupportSelection μ S u)
    (hSelectionT : ∀ u, HasIntegrableSupportSelection μ T u)
    (hDist : Integrable (fun ω => hausdorffDist (S ω) (T ω)) μ) :
    hausdorffDist (aumannExpectation μ S) (aumannExpectation μ T) ≤
      ∫ ω, hausdorffDist (S ω) (T ω) ∂μ := by
  have hASconv : Convex ℝ (aumannExpectation μ S) :=
    aumannExpectation_convex (Filter.Eventually.of_forall hSconv)
  have hATconv : Convex ℝ (aumannExpectation μ T) :=
    aumannExpectation_convex (Filter.Eventually.of_forall hTconv)
  apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
    hAScompact hATcompact hASne hATne hASconv hATconv
  · exact integral_nonneg fun _ => hausdorffDist_nonneg
  · intro u hu
    rw [supportFunction_aumannExpectation
      (Filter.Eventually.of_forall hScompact) hAScompact hASne u
      (hSupportS u) (hSelectionS u)]
    rw [supportFunction_aumannExpectation
      (Filter.Eventually.of_forall hTcompact) hATcompact hATne u
      (hSupportT u) (hSelectionT u)]
    calc
      |(∫ ω, supportFunction (S ω) u ∂μ) -
          ∫ ω, supportFunction (T ω) u ∂μ| =
          |∫ ω, supportFunction (S ω) u - supportFunction (T ω) u ∂μ| := by
            rw [integral_sub (hSupportS u) (hSupportT u)]
      _ ≤ ∫ ω, |supportFunction (S ω) u - supportFunction (T ω) u| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, hausdorffDist (S ω) (T ω) ∂μ := by
        apply integral_mono (hSupportS u |>.sub (hSupportT u) |>.abs) hDist
        intro ω
        calc
          |supportFunction (S ω) u - supportFunction (T ω) u| ≤
              ‖u‖ * hausdorffDist (S ω) (T ω) :=
            abs_supportFunction_sub_le_hausdorffDist
              (hScompact ω) (hTcompact ω) (hSne ω) (hTne ω) u
          _ ≤ 1 * hausdorffDist (S ω) (T ω) :=
            mul_le_mul_of_nonneg_right hu hausdorffDist_nonneg
          _ = hausdorffDist (S ω) (T ω) := one_mul _

/-- Automatic form of Hausdorff stability for the (unclosed) Aumann
expectations.  Once compactness of the two Aumann expectations is known,
Effros measurability and integrable envelopes construct all exact support
maximizers required by the elementary contraction theorem.-/
theorem hausdorffDist_aumannExpectation_le_integral_of_effros_of_envelope
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} {S T : Ω → Set E}
    (hSEffros : RandomSet.IsEffrosMeasurable S)
    (hTEffros : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    (hSconv : ∀ ω, Convex ℝ (S ω))
    (hTconv : ∀ ω, Convex ℝ (T ω))
    {gS gT : Ω → ℝ} (hgS : Integrable gS μ) (hgT : Integrable gT μ)
    (hdomS : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ gS ω)
    (hdomT : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ gT ω)
    (hAScompact : IsCompact (aumannExpectation μ S))
    (hATcompact : IsCompact (aumannExpectation μ T))
    (hDist : Integrable (fun ω => hausdorffDist (S ω) (T ω)) μ) :
    hausdorffDist (aumannExpectation μ S) (aumannExpectation μ T) ≤
      ∫ ω, hausdorffDist (S ω) (T ω) ∂μ := by
  have hSupportS : ∀ u,
      Integrable (fun ω => supportFunction (S ω) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hSEffros hScompact hSne hgS hdomS u
  have hSupportT : ∀ u,
      Integrable (fun ω => supportFunction (T ω) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hTEffros hTcompact hTne hgT hdomT u
  have hSelectionS : ∀ u, HasIntegrableSupportSelection μ S u := fun u =>
    hasIntegrableSupportSelection_of_effros_of_envelope
      hSEffros hScompact hSne hgS hdomS u
  have hSelectionT : ∀ u, HasIntegrableSupportSelection μ T u := fun u =>
    hasIntegrableSupportSelection_of_effros_of_envelope
      hTEffros hTcompact hTne hgT hdomT u
  have hASne : (aumannExpectation μ S).Nonempty := by
    rcases hSelectionS 0 with ⟨f, hf, _⟩
    exact aumannExpectation_nonempty_of_selection hf
  have hATne : (aumannExpectation μ T).Nonempty := by
    rcases hSelectionT 0 with ⟨f, hf, _⟩
    exact aumannExpectation_nonempty_of_selection hf
  exact hausdorffDist_aumannExpectation_le_integral
    hScompact hTcompact hSne hTne hSconv hTconv
    hAScompact hATcompact hASne hATne hSupportS hSupportT
    hSelectionS hSelectionT hDist

/-- Hausdorff contraction for the closures of Aumann expectations.  Effros
measurability and integrable envelopes now supply the support approximations
automatically, so no maximizing-selection hypotheses occur in the statement.-/
theorem hausdorffDist_closure_aumannExpectation_le_integral_of_envelope
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S T : Ω → Set E}
    (hSEffros : RandomSet.IsEffrosMeasurable S)
    (hTEffros : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    (hSconv : ∀ ω, Convex ℝ (S ω))
    (hTconv : ∀ ω, Convex ℝ (T ω))
    {gS gT : Ω → ℝ} (hgS : Integrable gS μ) (hgT : Integrable gT μ)
    (hdomS : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ gS ω)
    (hdomT : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ gT ω)
    (hAScompact : IsCompact (closure (aumannExpectation μ S)))
    (hATcompact : IsCompact (closure (aumannExpectation μ T)))
    (hDist : Integrable (fun ω => hausdorffDist (S ω) (T ω)) μ) :
    hausdorffDist (closure (aumannExpectation μ S))
        (closure (aumannExpectation μ T)) ≤
      ∫ ω, hausdorffDist (S ω) (T ω) ∂μ := by
  have hSupportS : ∀ u,
      Integrable (fun ω => supportFunction (S ω) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hSEffros hScompact hSne hgS hdomS u
  have hSupportT : ∀ u,
      Integrable (fun ω => supportFunction (T ω) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hTEffros hTcompact hTne hgT hdomT u
  have hfS : IsIntegrableSelection μ S
      (supportApproximateSelection hSEffros hScompact hSne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hSEffros hScompact hSne hgS hdomS 0 (by norm_num)
  have hfT : IsIntegrableSelection μ T
      (supportApproximateSelection hTEffros hTcompact hTne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hTEffros hTcompact hTne hgT hdomT 0 (by norm_num)
  have hASne : (closure (aumannExpectation μ S)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfS).closure
  have hATne : (closure (aumannExpectation μ T)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfT).closure
  have hASconv : Convex ℝ (closure (aumannExpectation μ S)) :=
    (aumannExpectation_convex (Filter.Eventually.of_forall hSconv)).closure
  have hATconv : Convex ℝ (closure (aumannExpectation μ T)) :=
    (aumannExpectation_convex (Filter.Eventually.of_forall hTconv)).closure
  apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
    hAScompact hATcompact hASne hATne hASconv hATconv
  · exact integral_nonneg fun _ => hausdorffDist_nonneg
  · intro u hu
    rw [supportFunction_closure_aumannExpectation_of_envelope
      hSEffros hScompact hSne hgS hdomS hAScompact u]
    rw [supportFunction_closure_aumannExpectation_of_envelope
      hTEffros hTcompact hTne hgT hdomT hATcompact u]
    calc
      |(∫ ω, supportFunction (S ω) u ∂μ) -
          ∫ ω, supportFunction (T ω) u ∂μ| =
          |∫ ω, supportFunction (S ω) u - supportFunction (T ω) u ∂μ| := by
            rw [integral_sub (hSupportS u) (hSupportT u)]
      _ ≤ ∫ ω, |supportFunction (S ω) u - supportFunction (T ω) u| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, hausdorffDist (S ω) (T ω) ∂μ := by
        apply integral_mono (hSupportS u |>.sub (hSupportT u) |>.abs) hDist
        intro ω
        calc
          |supportFunction (S ω) u - supportFunction (T ω) u| ≤
              ‖u‖ * hausdorffDist (S ω) (T ω) :=
            abs_supportFunction_sub_le_hausdorffDist
              (hScompact ω) (hTcompact ω) (hSne ω) (hTne ω) u
          _ ≤ 1 * hausdorffDist (S ω) (T ω) :=
            mul_le_mul_of_nonneg_right hu hausdorffDist_nonneg
          _ = hausdorffDist (S ω) (T ω) := one_mul _

/-- Finite-dimensional form of the contraction theorem: compactness of both
closed Aumann expectations follows automatically from the envelopes.-/
theorem hausdorffDist_closure_aumannExpectation_le_integral
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nonempty E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S T : Ω → Set E}
    (hSEffros : RandomSet.IsEffrosMeasurable S)
    (hTEffros : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    (hSconv : ∀ ω, Convex ℝ (S ω))
    (hTconv : ∀ ω, Convex ℝ (T ω))
    {gS gT : Ω → ℝ} (hgS : Integrable gS μ) (hgT : Integrable gT μ)
    (hdomS : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ gS ω)
    (hdomT : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ gT ω)
    (hDist : Integrable (fun ω => hausdorffDist (S ω) (T ω)) μ) :
    hausdorffDist (closure (aumannExpectation μ S))
        (closure (aumannExpectation μ T)) ≤
      ∫ ω, hausdorffDist (S ω) (T ω) ∂μ := by
  apply hausdorffDist_closure_aumannExpectation_le_integral_of_envelope
    hSEffros hTEffros hScompact hTcompact hSne hTne hSconv hTconv
    hgS hgT hdomS hdomT
  · exact closure_aumannExpectation_compact_of_integrable_envelope hgS
      (Filter.Eventually.of_forall hdomS)
  · exact closure_aumannExpectation_compact_of_integrable_envelope hgT
      (Filter.Eventually.of_forall hdomT)
  · exact hDist

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
