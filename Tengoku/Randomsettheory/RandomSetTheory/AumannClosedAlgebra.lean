/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosMinkowski
import Tengoku.Randomsettheory.RandomSetTheory.SupportSelection
import Tengoku.Randomsettheory.RandomSetTheory.Geometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed convex algebra of the Aumann expectation

The Aumann expectation always satisfies the easy Minkowski inclusion, while
the reverse inclusion for the unclosed expectation asks for a measurable
decomposition of every selection of a pointwise sum.  This file deliberately
avoids postulating such a decomposition.  Under the standard compact-valued
Effros and integrable-envelope hypotheses, closed convexification is exactly
Minkowski additive.  The proof identifies support functions and uses their
uniqueness on compact nonempty convex sets.

We also record exact compatibility with deterministic homotheties, including
the zero scalar.  The nonzero case follows already at the level of selections;
the zero case uses the nonemptiness supplied by measurable selection.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory
open scoped Pointwise InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-! ## Deterministic closed-convex algebra -/

/-- Closed convexification commutes with scalar multiplication.-/
theorem closedConvexHull_smul_set_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (K : Set E) :
    closedConvexHull ℝ (c • K) = c • closedConvexHull ℝ K := by
  rw [closedConvexHull_eq_closure_convexHull, convexHull_smul,
    closure_smul₀, closedConvexHull_eq_closure_convexHull]

/-! ## Minkowski additivity after closure and convexification -/

/-- Closed convexified Aumann expectation is Minkowski additive.

No measurable decomposition of a selection of `S ω + T ω` is assumed.  The
proof instead combines the exact support identity for closed Aumann
expectations with pointwise Minkowski additivity of support functions.-/
theorem closedConvexHull_closure_aumannExpectation_add
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S T : Ω → Set H}
    (hSEffros : RandomSet.IsEffrosMeasurable S)
    (hTEffros : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty)
    {gS gT : Ω → ℝ} (hgS : Integrable gS μ) (hgT : Integrable gT μ)
    (hdomS : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ gS ω)
    (hdomT : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ gT ω) :
    closedConvexHull ℝ
        (closure (aumannExpectation μ (fun ω => S ω + T ω))) =
      closedConvexHull ℝ (closure (aumannExpectation μ S)) +
        closedConvexHull ℝ (closure (aumannExpectation μ T)) := by
  have hSTEffros : RandomSet.IsEffrosMeasurable
      (fun ω => S ω + T ω) :=
    hSEffros.add hTEffros
      (fun ω => (hScompact ω).isClosed)
      (fun ω => (hTcompact ω).isClosed) hSne hTne
  have hSTcompact : ∀ ω, IsCompact (S ω + T ω) := fun ω =>
    (hScompact ω).add (hTcompact ω)
  have hSTne : ∀ ω, (S ω + T ω).Nonempty := fun ω =>
    (hSne ω).add (hTne ω)
  have hgST : Integrable (fun ω => gS ω + gT ω) μ := hgS.add hgT
  have hdomST : ∀ ω, ∀ z ∈ S ω + T ω,
      ‖z‖ ≤ gS ω + gT ω := by
    intro ω z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    exact (norm_add_le x y).trans
      (add_le_add (hdomS ω x hx) (hdomT ω y hy))
  have hAScompact : IsCompact (closure (aumannExpectation μ S)) :=
    closure_aumannExpectation_compact_of_integrable_envelope hgS
      (Filter.Eventually.of_forall hdomS)
  have hATcompact : IsCompact (closure (aumannExpectation μ T)) :=
    closure_aumannExpectation_compact_of_integrable_envelope hgT
      (Filter.Eventually.of_forall hdomT)
  have hASTcompact : IsCompact
      (closure (aumannExpectation μ (fun ω => S ω + T ω))) :=
    closure_aumannExpectation_compact_of_integrable_envelope hgST
      (Filter.Eventually.of_forall hdomST)
  have hfS : IsIntegrableSelection μ S
      (supportApproximateSelection hSEffros hScompact hSne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hSEffros hScompact hSne hgS hdomS 0 (by norm_num)
  have hfT : IsIntegrableSelection μ T
      (supportApproximateSelection hTEffros hTcompact hTne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hTEffros hTcompact hTne hgT hdomT 0 (by norm_num)
  have hfST : IsIntegrableSelection μ (fun ω => S ω + T ω)
      (supportApproximateSelection
        hSTEffros hSTcompact hSTne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hSTEffros hSTcompact hSTne hgST hdomST 0 (by norm_num)
  have hASne : (closure (aumannExpectation μ S)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfS).closure
  have hATne : (closure (aumannExpectation μ T)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfT).closure
  have hASTne :
      (closure (aumannExpectation μ (fun ω => S ω + T ω))).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfST).closure
  have hCScompact : IsCompact
      (closedConvexHull ℝ (closure (aumannExpectation μ S))) :=
    closedConvexHull_compact hAScompact
  have hCTcompact : IsCompact
      (closedConvexHull ℝ (closure (aumannExpectation μ T))) :=
    closedConvexHull_compact hATcompact
  have hCSne :
      (closedConvexHull ℝ (closure (aumannExpectation μ S))).Nonempty :=
    hASne.mono subset_closedConvexHull
  have hCTne :
      (closedConvexHull ℝ (closure (aumannExpectation μ T))).Nonempty :=
    hATne.mono subset_closedConvexHull
  have hSupportS : ∀ u : H,
      Integrable (fun ω => supportFunction (S ω) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hSEffros hScompact hSne hgS hdomS u
  have hSupportT : ∀ u : H,
      Integrable (fun ω => supportFunction (T ω) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hTEffros hTcompact hTne hgT hdomT u
  apply eq_of_supportFunction_eq
    (closedConvexHull_compact hASTcompact)
    (hCScompact.add hCTcompact)
    (hASTne.mono subset_closedConvexHull)
    (hCSne.add hCTne)
    convex_closedConvexHull
    (convex_closedConvexHull.add convex_closedConvexHull)
  intro u
  calc
    supportFunction
        (closedConvexHull ℝ
          (closure (aumannExpectation μ (fun ω => S ω + T ω)))) u =
        supportFunction
          (closure (aumannExpectation μ (fun ω => S ω + T ω))) u :=
      supportFunction_closedConvexHull hASTcompact hASTne u
    _ = ∫ ω, supportFunction (S ω + T ω) u ∂μ :=
      supportFunction_closure_aumannExpectation_of_envelope
        hSTEffros hSTcompact hSTne hgST hdomST hASTcompact u
    _ = ∫ ω, supportFunction (S ω) u + supportFunction (T ω) u ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact supportFunction_add
        (hScompact ω) (hTcompact ω) (hSne ω) (hTne ω) u
    _ = (∫ ω, supportFunction (S ω) u ∂μ) +
        ∫ ω, supportFunction (T ω) u ∂μ :=
      integral_add (hSupportS u) (hSupportT u)
    _ = supportFunction (closure (aumannExpectation μ S)) u +
        supportFunction (closure (aumannExpectation μ T)) u := by
      rw [supportFunction_closure_aumannExpectation_of_envelope
          hSEffros hScompact hSne hgS hdomS hAScompact u,
        supportFunction_closure_aumannExpectation_of_envelope
          hTEffros hTcompact hTne hgT hdomT hATcompact u]
    _ = supportFunction
          (closedConvexHull ℝ (closure (aumannExpectation μ S))) u +
        supportFunction
          (closedConvexHull ℝ (closure (aumannExpectation μ T))) u := by
      rw [supportFunction_closedConvexHull hAScompact hASne u,
        supportFunction_closedConvexHull hATcompact hATne u]
    _ = supportFunction
        (closedConvexHull ℝ (closure (aumannExpectation μ S)) +
          closedConvexHull ℝ (closure (aumannExpectation μ T))) u :=
      (supportFunction_add hCScompact hCTcompact hCSne hCTne u).symm

/-! ## Homotheties -/

/-- Closed convexified Aumann expectation commutes with every deterministic
scalar multiplication.  For `c ≠ 0`, this is already exact before taking
closures.  For `c = 0`, nonemptiness of the Effros correspondence ensures
that both sides reduce to the singleton `{0}`.-/
theorem closedConvexHull_closure_aumannExpectation_smul
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → Set H}
    (hSEffros : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) (c : ℝ) :
    closedConvexHull ℝ
        (closure (aumannExpectation μ (fun ω => c • S ω))) =
      c • closedConvexHull ℝ (closure (aumannExpectation μ S)) := by
  by_cases hc : c = 0
  · subst c
    have hfS : IsIntegrableSelection μ S
        (supportApproximateSelection
          hSEffros hScompact hSne 0 1 (by norm_num)) :=
      integrableSelection_supportApproximateSelection_of_envelope
        hSEffros hScompact hSne hg hdom 0 (by norm_num)
    have hASne : (closure (aumannExpectation μ S)).Nonempty :=
      (aumannExpectation_nonempty_of_selection hfS).closure
    have hCSne :
        (closedConvexHull ℝ (closure (aumannExpectation μ S))).Nonempty :=
      hASne.mono subset_closedConvexHull
    have hzeroCorrespondence :
        (fun ω => (0 : ℝ) • S ω) =
          (fun _ : Ω => ({0} : Set H)) := by
      funext ω
      exact zero_smul_set (hSne ω)
    have hzeroAumann :
        aumannExpectation μ (fun ω => (0 : ℝ) • S ω) = ({0} : Set H) := by
      rw [hzeroCorrespondence]
      have hsingleton := aumannExpectation_singleton
        (μ := μ) (f := fun _ : Ω => (0 : H)) (integrable_zero Ω H μ)
      simpa using hsingleton
    rw [hzeroAumann, closure_singleton]
    have hzeroHull : closedConvexHull ℝ ({0} : Set H) = {0} := by
      apply Set.Subset.antisymm
      · exact closedConvexHull_min Subset.rfl
          (convex_singleton 0) isClosed_singleton
      · exact subset_closedConvexHull
    rw [hzeroHull]
    exact Set.singleton_zero.trans (zero_smul_set hCSne).symm
  · rw [aumannExpectation_smul_of_ne c hc, closure_smul₀,
      closedConvexHull_smul_set_eq]

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
