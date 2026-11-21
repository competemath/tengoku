/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSupport
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable support maximizers

For a compact-valued Effros-measurable correspondence, the correspondence of
points maximizing a fixed continuous linear functional is itself Effros
measurable.  The proof uses a countable family of balls around a dense
sequence and closed localizations.  Kuratowski--Ryll-Nardzewski then provides
an exact measurable maximizer.  Under an integrable envelope this maximizer
is an integrable selection, discharging the support-selection hypothesis in
the Aumann support theorem.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- Points of a fibre attaining the support in direction `u`.-/
def supportArgmax {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Ω → Set H) (u : H) (ω : Ω) : Set H :=
  S ω ∩ {x | ⟪u, x⟫_ℝ = supportFunction (S ω) u}

theorem supportArgmax_nonempty
    {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Ω → Set H} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty) (u : H) (ω : Ω) :
    (supportArgmax S u ω).Nonempty := by
  obtain ⟨x, hx, hxmax⟩ := supportFunction_attains (hcompact ω) (hne ω) u
  exact ⟨x, hx, hxmax.symm⟩

theorem supportArgmax_isCompact
    {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Ω → Set H} (hcompact : ∀ ω, IsCompact (S ω))
    (u : H) (ω : Ω) : IsCompact (supportArgmax S u ω) := by
  exact (hcompact ω).inter_right
    (isClosed_eq (by fun_prop : Continuous fun x : H => ⟪u, x⟫_ℝ) continuous_const)

theorem supportArgmax_subset
    {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Ω → Set H) (u : H) (ω : Ω) : supportArgmax S u ω ⊆ S ω :=
  inter_subset_left

/-- Balls with centres in the canonical dense sequence and inverse-natural
radii form a shrinking basis whose closed balls still fit inside an open
neighbourhood.-/
theorem exists_denseSeq_ball_closedBall_subset
    {H : Type*} [MetricSpace H] [SecondCountableTopology H] [Nonempty H]
    {U : Set H} (hU : IsOpen U) {x : H} (hx : x ∈ U) :
    ∃ n m : ℕ,
      x ∈ Metric.ball (denseSeq H n) (1 / (m + 1 : ℝ)) ∧
        Metric.closedBall (denseSeq H n) (1 / (m + 1 : ℝ)) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (Metric.isOpen_iff.mp hU) x hx
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hδ)
  let r : ℝ := 1 / (m + 1 : ℝ)
  have hr : 0 < r := by positivity
  obtain ⟨n, hn⟩ := (denseRange_denseSeq H).exists_dist_lt x hr
  refine ⟨n, m, ?_, ?_⟩
  · simpa [r, Metric.mem_ball, dist_comm] using hn
  · apply (Metric.closedBall_subset_ball' (x := denseSeq H n) (y := x) ?_).trans hδU
    calc
      r + dist (denseSeq H n) x < r + r := by
        rw [dist_comm]
        linarith
      _ < δ := by
        dsimp [r]
        linarith

/-- The countable event witnessing that the support argmax hits `U` through
a localized closed ball.-/
def SupportArgmaxBasisEvent
    {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [SecondCountableTopology H] [Nonempty H]
    (S : Ω → Set H) (u : H) (U : Set H) (n m : ℕ) (ω : Ω) : Prop :=
  Metric.closedBall (denseSeq H n) (1 / (m + 1 : ℝ)) ⊆ U ∧
    (S ω ∩ Metric.ball (denseSeq H n) (1 / (m + 1 : ℝ))).Nonempty ∧
      supportFunction
          (castaingLocalization S (denseSeq H n) (1 / (m + 1 : ℝ)) ω) u =
        supportFunction (S ω) u

theorem measurableSet_supportArgmaxBasisEvent
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) (U : Set H) (n m : ℕ) :
    MeasurableSet {ω | SupportArgmaxBasisEvent S u U n m ω} := by
  let q : H := denseSeq H n
  let r : ℝ := 1 / (m + 1 : ℝ)
  have hhit : MeasurableSet {ω | (S ω ∩ Metric.ball q r).Nonempty} :=
    hS (Metric.ball q r) Metric.isOpen_ball
  have hlocal : Measurable
      (fun ω => supportFunction (castaingLocalization S q r ω) u) :=
    measurable_supportFunction (effros_castaingLocalization hS q r)
      (castaingLocalization_isCompact hcompact q r)
      (castaingLocalization_nonempty hne q r) u
  have hglobal : Measurable (fun ω => supportFunction (S ω) u) :=
    measurable_supportFunction hS hcompact hne u
  by_cases hb : Metric.closedBall q r ⊆ U
  · have hEq : {ω | SupportArgmaxBasisEvent S u U n m ω} =
        {ω | (S ω ∩ Metric.ball q r).Nonempty} ∩
          {ω | supportFunction (castaingLocalization S q r ω) u =
            supportFunction (S ω) u} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨_, hhitω, heqω⟩
        exact ⟨hhitω, heqω⟩
      · rintro ⟨hhitω, heqω⟩
        exact ⟨by simpa [q, r] using hb, hhitω, by simpa [q, r] using heqω⟩
    rw [hEq]
    exact hhit.inter (measurableSet_eq_fun hlocal hglobal)
  · have hempty : {ω | SupportArgmaxBasisEvent S u U n m ω} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · intro hω
        exact (hb (by simpa [q, r] using hω.1)).elim
      · exact False.elim
    rw [hempty]
    exact MeasurableSet.empty

/-- The support-argmax correspondence of a compact random set is Effros
measurable.-/
theorem effrosMeasurable_supportArgmax
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) : RandomSet.IsEffrosMeasurable (supportArgmax S u) := by
  intro U hU
  have hEq : {ω | (supportArgmax S u ω ∩ U).Nonempty} =
      ⋃ n : ℕ, ⋃ m : ℕ, {ω | SupportArgmaxBasisEvent S u U n m ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxmax, hxU⟩
      obtain ⟨n, m, hxball, hclosedBall⟩ :=
        exists_denseSeq_ball_closedBall_subset hU hxU
      let q : H := denseSeq H n
      let r : ℝ := 1 / (m + 1 : ℝ)
      have hhit : (S ω ∩ Metric.ball q r).Nonempty :=
        ⟨x, hxmax.1, by simpa [q, r] using hxball⟩
      have hxlocal : x ∈ castaingLocalization S q r ω := by
        rw [castaingLocalization, ite_eq_left hhit]
        exact subset_closure ⟨hxmax.1, by simpa [q, r] using hxball⟩
      have hlocalCompact := castaingLocalization_isCompact hcompact q r ω
      have hlocalNe := castaingLocalization_nonempty hne q r ω
      have hlocalSub := castaingLocalization_subset
        (fun ω => (hcompact ω).isClosed) q r ω
      refine ⟨n, m, ?_⟩
      refine ⟨by simpa [q, r] using hclosedBall, hhit, ?_⟩
      apply le_antisymm
      · exact supportFunction_mono hlocalCompact (hcompact ω) hlocalNe hlocalSub u
      · calc
          supportFunction (S ω) u = ⟪u, x⟫_ℝ := hxmax.2.symm
          _ ≤ supportFunction (castaingLocalization S q r ω) u :=
            inner_le_supportFunction hlocalCompact hxlocal u
    · rintro ⟨n, m, hbasis, hhit, heq⟩
      let q : H := denseSeq H n
      let r : ℝ := 1 / (m + 1 : ℝ)
      have hhit' : (S ω ∩ Metric.ball q r).Nonempty := by
        simpa [q, r] using hhit
      have hlocalCompact := castaingLocalization_isCompact hcompact q r ω
      have hlocalNe := castaingLocalization_nonempty hne q r ω
      obtain ⟨y, hy, hymax⟩ := supportFunction_attains hlocalCompact hlocalNe u
      have hyS : y ∈ S ω :=
        castaingLocalization_subset (fun ω => (hcompact ω).isClosed) q r ω hy
      have hyclosure : y ∈ closure (S ω ∩ Metric.ball q r) := by
        simpa [castaingLocalization, hhit'] using hy
      have hyball : y ∈ Metric.closedBall q r :=
        closure_minimal (inter_subset_right.trans Metric.ball_subset_closedBall)
          Metric.isClosed_closedBall hyclosure
      refine ⟨y, ⟨hyS, ?_⟩, ?_⟩
      · calc
          ⟪u, y⟫_ℝ = supportFunction (castaingLocalization S q r ω) u := hymax.symm
          _ = supportFunction (S ω) u := by simpa [q, r] using heq
      · have hbasis' : Metric.closedBall q r ⊆ U := by
          simpa [q, r] using hbasis
        exact hbasis' hyball
  rw [hEq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_supportArgmaxBasisEvent hS hcompact hne u U n m

/-- Canonical exact measurable support maximizer.-/
def supportMaximizingSelection
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) : Ω → H :=
  krnSelection (effrosMeasurable_supportArgmax hS hcompact hne u)
    (supportArgmax_nonempty hcompact hne u)

theorem measurable_supportMaximizingSelection
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) : Measurable (supportMaximizingSelection hS hcompact hne u) :=
  (kuratowski_ryll_nardzewski
    (effrosMeasurable_supportArgmax hS hcompact hne u)
    (fun ω => (supportArgmax_isCompact hcompact u ω).isClosed)
    (supportArgmax_nonempty hcompact hne u)).1

theorem supportMaximizingSelection_mem_and_inner_eq
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) (ω : Ω) :
    supportMaximizingSelection hS hcompact hne u ω ∈ S ω ∧
      ⟪u, supportMaximizingSelection hS hcompact hne u ω⟫_ℝ =
        supportFunction (S ω) u :=
  (kuratowski_ryll_nardzewski
    (effrosMeasurable_supportArgmax hS hcompact hne u)
    (fun ω => (supportArgmax_isCompact hcompact u ω).isClosed)
    (supportArgmax_nonempty hcompact hne u)).2 ω

/-- An integrable envelope makes the exact measurable support maximizer an
integrable selection, hence provides `HasIntegrableSupportSelection`.-/
theorem hasIntegrableSupportSelection_of_effros_of_envelope
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {μ : Measure Ω} {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) (u : H) :
    HasIntegrableSupportSelection μ S u := by
  let f := supportMaximizingSelection hS hcompact hne u
  have hfmeas : Measurable f :=
    measurable_supportMaximizingSelection hS hcompact hne u
  have hfprop : ∀ ω, f ω ∈ S ω ∧ ⟪u, f ω⟫_ℝ = supportFunction (S ω) u :=
    supportMaximizingSelection_mem_and_inner_eq hS hcompact hne u
  have hfint : Integrable f μ := by
    apply hg.mono' hfmeas.aestronglyMeasurable
    filter_upwards [] with ω
    exact hdom ω (f ω) (hfprop ω).1
  exact ⟨f, ⟨hfint, Filter.Eventually.of_forall fun ω => (hfprop ω).1⟩,
    Filter.Eventually.of_forall fun ω => (hfprop ω).2⟩

/-- Exact support representation of the Aumann expectation.  Effros
measurability, compact nonempty values, and an integrable envelope now
construct the maximizing selection internally; no separate measurable
maximum hypothesis is needed.-/
theorem supportFunction_aumannExpectation_of_effros_of_envelope
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {μ : Measure Ω} {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hAcompact : IsCompact (aumannExpectation μ S)) (u : H) :
    supportFunction (aumannExpectation μ S) u =
      ∫ ω, supportFunction (S ω) u ∂μ := by
  rcases hasIntegrableSupportSelection_of_effros_of_envelope
      hS hcompact hne hg hdom u with ⟨f, hf, hmax⟩
  exact supportFunction_aumannExpectation
    (Filter.Eventually.of_forall hcompact) hAcompact
    (aumannExpectation_nonempty_of_selection hf) u
    (integrable_supportFunction_of_envelope hS hcompact hne hg hdom u)
    ⟨f, hf, hmax⟩

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
