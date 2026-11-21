/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosOperations
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableGraphTheorem
import Tengoku.Randomsettheory.RandomSetTheory.KuratowskiRyllNardzewski
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableMaximum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable decomposition of selections of Minkowski sums

For compact nonempty Effros-measurable correspondences `S` and `T`, this
file constructs a measurable pair minimizing the residual
`dist (x + y) (h ω)` over `S ω × T ω`.  If `h ω ∈ S ω + T ω`, the minimum is
zero and the selected pair is an exact decomposition of `h ω`.  Integrable
envelopes then make both coordinates integrable and discharge
`HasIntegrableMinkowskiDecomposition`.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace
open scoped Pointwise Topology

noncomputable section

namespace RandomSetTheory

/-- Compact pairs minimizing the error in decomposing `h ω` as a point of
the pointwise Minkowski sum.  This correspondence is nonempty even away from
the event `h ω ∈ S ω + T ω`, which avoids any global nonemptiness issue.-/
def minkowskiDecompositionArgmin
    {Ω E : Type*} [PseudoMetricSpace E] [Add E]
    (S T : Ω → Set E) (h : Ω → E) (ω : Ω) : Set (E × E) :=
  (S ω ×ˢ T ω) ∩
    {p | dist (p.1 + p.2) (h ω) = infDist (h ω) (S ω + T ω)}

theorem minkowskiDecompositionArgmin_subset
    {Ω E : Type*} [PseudoMetricSpace E] [Add E]
    (S T : Ω → Set E) (h : Ω → E) (ω : Ω) :
    minkowskiDecompositionArgmin S T h ω ⊆ S ω ×ˢ T ω :=
  inter_subset_left

theorem minkowskiDecompositionArgmin_isCompact
    {Ω E : Type*} [NormedAddCommGroup E]
    {S T : Ω → Set E} (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω)) (h : Ω → E) (ω : Ω) :
    IsCompact (minkowskiDecompositionArgmin S T h ω) := by
  apply (hScompact ω).prod (hTcompact ω) |>.inter_right
  exact isClosed_eq
    ((continuous_fst.add continuous_snd).dist continuous_const)
    continuous_const

theorem minkowskiDecompositionArgmin_nonempty
    {Ω E : Type*} [NormedAddCommGroup E]
    {S T : Ω → Set E} (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    (h : Ω → E) (ω : Ω) :
    (minkowskiDecompositionArgmin S T h ω).Nonempty := by
  have hsumCompact : IsCompact (S ω + T ω) :=
    (hScompact ω).add (hTcompact ω)
  have hsumNe : (S ω + T ω).Nonempty := (hSne ω).add (hTne ω)
  obtain ⟨z, hz, hzmin⟩ := hsumCompact.exists_infDist_eq_dist hsumNe (h ω)
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  refine ⟨(x, y), ⟨hx, hy⟩, ?_⟩
  simpa [dist_comm] using hzmin.symm

/-- Countable basis event used to prove Effros measurability of the residual
argmin correspondence.-/
def MinkowskiArgminBasisEvent
    {Ω E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology (E × E)] [Nonempty (E × E)]
    (S T : Ω → Set E) (h : Ω → E) (U : Set (E × E))
    (n m : ℕ) (ω : Ω) : Prop :=
  let P : Ω → Set (E × E) := fun ω => S ω ×ˢ T ω
  let q : E × E := denseSeq (E × E) n
  let r : ℝ := 1 / (m + 1 : ℝ)
  Metric.closedBall q r ⊆ U ∧
    (P ω ∩ Metric.ball q r).Nonempty ∧
      infDist (h ω)
          ((fun p : E × E => p.1 + p.2) '' castaingLocalization P q r ω) =
        infDist (h ω) (S ω + T ω)

/-- The distance to an Effros-measurable closed correspondence remains
measurable when the point at which it is evaluated also depends measurably on
the base point.-/
theorem measurable_infDist_correspondence_comp
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {Q : Ω → Set E} (hQ : RandomSet.IsEffrosMeasurable Q)
    (hQclosed : ∀ ω, IsClosed (Q ω)) (hQne : ∀ ω, (Q ω).Nonempty)
    {h : Ω → E} (hh : Measurable h) :
    Measurable (fun ω => infDist (h ω) (Q ω)) := by
  let f : ℕ → Ω → E := castaingRepresentation hQ hQclosed hQne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hQ hQclosed hQne
  have hclosure : ∀ ω, closure (Set.range fun n => f n ω) = Q ω :=
    closure_range_castaingRepresentation hQ hQclosed hQne
  have hEq : (fun ω => infDist (h ω) (Q ω)) =
      fun ω => ⨅ n : ℕ, dist (h ω) (f n ω) := by
    funext ω
    rw [← hclosure ω, Metric.infDist_closure]
    rw [Metric.infDist_eq_iInf, iInf, iInf]
    apply congrArg sInf
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨n, hn⟩ := y.property
      exact ⟨n, congrArg (dist (h ω)) hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨⟨f n ω, ⟨n, rfl⟩⟩, rfl⟩
  rw [hEq]
  exact Measurable.iInf fun n => hh.dist (hf n)

set_option maxHeartbeats 800000 in
-- The nested product correspondence and its two localized distance maps make
-- elaboration substantially heavier than the scalar support-argmax analogue.
theorem measurableSet_minkowskiArgminBasisEvent
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h)
    (U : Set (E × E)) (n m : ℕ) :
    MeasurableSet {ω | MinkowskiArgminBasisEvent S T h U n m ω} := by
  let P : Ω → Set (E × E) := fun ω => S ω ×ˢ T ω
  let addMap : E × E → E := fun p => p.1 + p.2
  let q : E × E := denseSeq (E × E) n
  let r : ℝ := 1 / (m + 1 : ℝ)
  have hPcompact : ∀ ω, IsCompact (P ω) := fun ω =>
    (hScompact ω).prod (hTcompact ω)
  have hPne : ∀ ω, (P ω).Nonempty := fun ω => (hSne ω).prod (hTne ω)
  have hPEffros : RandomSet.IsEffrosMeasurable P :=
    hS.prod hT (fun ω => (hScompact ω).isClosed)
      (fun ω => (hTcompact ω).isClosed) hSne hTne
  have haddContinuous : Continuous addMap := continuous_fst.add continuous_snd
  have hlocalEffros : RandomSet.IsEffrosMeasurable
      (fun ω => addMap '' castaingLocalization P q r ω) :=
    (effros_castaingLocalization hPEffros q r).image haddContinuous
  have hlocalCompact : ∀ ω,
      IsCompact (addMap '' castaingLocalization P q r ω) := fun ω =>
    (castaingLocalization_isCompact hPcompact q r ω).image haddContinuous
  have hlocalNe : ∀ ω,
      (addMap '' castaingLocalization P q r ω).Nonempty := fun ω =>
    (castaingLocalization_nonempty hPne q r ω).image addMap
  have hlocalDist : Measurable (fun ω =>
      infDist (h ω) (addMap '' castaingLocalization P q r ω)) := by
    exact measurable_infDist_correspondence_comp hlocalEffros
      (fun ω => (hlocalCompact ω).isClosed) hlocalNe hh
  have hsumEffros : RandomSet.IsEffrosMeasurable (fun ω => S ω + T ω) :=
    hS.add hT (fun ω => (hScompact ω).isClosed)
      (fun ω => (hTcompact ω).isClosed) hSne hTne
  have hsumCompact : ∀ ω, IsCompact (S ω + T ω) := fun ω =>
    (hScompact ω).add (hTcompact ω)
  have hsumNe : ∀ ω, (S ω + T ω).Nonempty := fun ω =>
    (hSne ω).add (hTne ω)
  have hglobalDist : Measurable (fun ω => infDist (h ω) (S ω + T ω)) := by
    exact measurable_infDist_correspondence_comp hsumEffros
      (fun ω => (hsumCompact ω).isClosed) hsumNe hh
  have hhit : MeasurableSet {ω | (P ω ∩ Metric.ball q r).Nonempty} :=
    hPEffros (Metric.ball q r) Metric.isOpen_ball
  by_cases hb : Metric.closedBall q r ⊆ U
  · have hEq : {ω | MinkowskiArgminBasisEvent S T h U n m ω} =
        {ω | (P ω ∩ Metric.ball q r).Nonempty} ∩
          {ω | infDist (h ω)
              (addMap '' castaingLocalization P q r ω) =
            infDist (h ω) (S ω + T ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨_, hhitω, heqω⟩
        exact ⟨hhitω, by simpa [P, addMap, q, r] using heqω⟩
      · rintro ⟨hhitω, heqω⟩
        exact ⟨by simpa [q, r] using hb, by simpa [P, q, r] using hhitω,
          by simpa [P, addMap, q, r] using heqω⟩
    rw [hEq]
    exact hhit.inter (measurableSet_eq_fun hlocalDist hglobalDist)
  · have hempty : {ω | MinkowskiArgminBasisEvent S T h U n m ω} =
        (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · intro hω
        exact (hb (by simpa [q, r] using hω.1)).elim
      · exact False.elim
    rw [hempty]
    exact MeasurableSet.empty

/-- The correspondence of pairs minimizing the residual of a prescribed
measurable target is Effros measurable.-/
theorem effrosMeasurable_minkowskiDecompositionArgmin
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h) :
    RandomSet.IsEffrosMeasurable (minkowskiDecompositionArgmin S T h) := by
  intro U hU
  have hEq : {ω | (minkowskiDecompositionArgmin S T h ω ∩ U).Nonempty} =
      ⋃ n : ℕ, ⋃ m : ℕ, {ω | MinkowskiArgminBasisEvent S T h U n m ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨p, hpmin, hpU⟩
      obtain ⟨n, m, hpball, hclosedBall⟩ :=
        exists_denseSeq_ball_closedBall_subset hU hpU
      let P : Ω → Set (E × E) := fun ω => S ω ×ˢ T ω
      let addMap : E × E → E := fun p => p.1 + p.2
      let q : E × E := denseSeq (E × E) n
      let r : ℝ := 1 / (m + 1 : ℝ)
      have hPcompact : ∀ ω, IsCompact (P ω) := fun ω =>
        (hScompact ω).prod (hTcompact ω)
      have hPne : ∀ ω, (P ω).Nonempty := fun ω =>
        (hSne ω).prod (hTne ω)
      have hhit : (P ω ∩ Metric.ball q r).Nonempty :=
        ⟨p, hpmin.1, by simpa [q, r] using hpball⟩
      have hplocal : p ∈ castaingLocalization P q r ω := by
        rw [castaingLocalization, ite_eq_left hhit]
        exact subset_closure ⟨hpmin.1, by simpa [q, r] using hpball⟩
      have hlocalCompact := castaingLocalization_isCompact hPcompact q r ω
      have hlocalNe := castaingLocalization_nonempty hPne q r ω
      have hlocalSub := castaingLocalization_subset
        (fun ω => (hPcompact ω).isClosed) q r ω
      have hlocalImageNe : (addMap '' castaingLocalization P q r ω).Nonempty :=
        hlocalNe.image addMap
      have hlocalImageSub : addMap '' castaingLocalization P q r ω ⊆
          S ω + T ω := by
        rintro _ ⟨a, ha, rfl⟩
        have haP : a ∈ P ω := hlocalSub ha
        exact Set.add_mem_add haP.1 haP.2
      refine ⟨n, m, ?_⟩
      refine ⟨by simpa [q, r] using hclosedBall, hhit, ?_⟩
      apply le_antisymm
      · calc
          infDist (h ω) (addMap '' castaingLocalization P q r ω) ≤
              dist (h ω) (addMap p) :=
            infDist_le_dist_of_mem ⟨p, hplocal, rfl⟩
          _ = dist (p.1 + p.2) (h ω) := by simp [addMap, dist_comm]
          _ = infDist (h ω) (S ω + T ω) := hpmin.2
      · exact infDist_le_infDist_of_subset hlocalImageSub hlocalImageNe
    · rintro ⟨n, m, hbasis, hhit, heq⟩
      let P : Ω → Set (E × E) := fun ω => S ω ×ˢ T ω
      let addMap : E × E → E := fun p => p.1 + p.2
      let q : E × E := denseSeq (E × E) n
      let r : ℝ := 1 / (m + 1 : ℝ)
      have hPcompact : ∀ ω, IsCompact (P ω) := fun ω =>
        (hScompact ω).prod (hTcompact ω)
      have hPne : ∀ ω, (P ω).Nonempty := fun ω =>
        (hSne ω).prod (hTne ω)
      have hhit' : (P ω ∩ Metric.ball q r).Nonempty := by
        simpa [P, q, r] using hhit
      have hlocalCompact := castaingLocalization_isCompact hPcompact q r ω
      have hlocalNe := castaingLocalization_nonempty hPne q r ω
      have haddContinuous : Continuous addMap := continuous_fst.add continuous_snd
      have hlocalImageCompact :
          IsCompact (addMap '' castaingLocalization P q r ω) :=
        hlocalCompact.image haddContinuous
      have hlocalImageNe : (addMap '' castaingLocalization P q r ω).Nonempty :=
        hlocalNe.image addMap
      obtain ⟨z, hz, hzmin⟩ :=
        hlocalImageCompact.exists_infDist_eq_dist hlocalImageNe (h ω)
      rcases hz with ⟨p, hplocal, rfl⟩
      have hpP : p ∈ P ω :=
        castaingLocalization_subset
          (fun ω => (hPcompact ω).isClosed) q r ω hplocal
      have hpclosure : p ∈ closure (P ω ∩ Metric.ball q r) := by
        simpa [castaingLocalization, hhit'] using hplocal
      have hpclosedBall : p ∈ Metric.closedBall q r :=
        closure_minimal
          (inter_subset_right.trans Metric.ball_subset_closedBall)
          Metric.isClosed_closedBall hpclosure
      refine ⟨p, ⟨hpP, ?_⟩, ?_⟩
      · calc
          dist (p.1 + p.2) (h ω) = dist (h ω) (addMap p) := by
            simp [addMap, dist_comm]
          _ = infDist (h ω) (addMap '' castaingLocalization P q r ω) :=
            hzmin.symm
          _ = infDist (h ω) (S ω + T ω) := by
            simpa [P, addMap, q, r] using heq
      · have hbasis' : Metric.closedBall q r ⊆ U := by
          simpa [q, r] using hbasis
        exact hbasis' hpclosedBall
  rw [hEq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_minkowskiArgminBasisEvent
      hS hT hScompact hTcompact hSne hTne hh U n m

/-- Canonical measurable pair minimizing the residual of a measurable target
over the product correspondence.-/
def minkowskiDecompositionSelection
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h) : Ω → E × E :=
  krnSelection
    (effrosMeasurable_minkowskiDecompositionArgmin
      hS hT hScompact hTcompact hSne hTne hh)
    (minkowskiDecompositionArgmin_nonempty
      hScompact hTcompact hSne hTne h)

theorem measurable_minkowskiDecompositionSelection
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h) :
    Measurable
      (minkowskiDecompositionSelection
        hS hT hScompact hTcompact hSne hTne hh) :=
  (kuratowski_ryll_nardzewski
    (effrosMeasurable_minkowskiDecompositionArgmin
      hS hT hScompact hTcompact hSne hTne hh)
    (fun ω =>
      (minkowskiDecompositionArgmin_isCompact hScompact hTcompact h ω).isClosed)
    (minkowskiDecompositionArgmin_nonempty
      hScompact hTcompact hSne hTne h)).1

theorem minkowskiDecompositionSelection_mem_and_residual_eq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h) (ω : Ω) :
    let p := minkowskiDecompositionSelection
      hS hT hScompact hTcompact hSne hTne hh ω
    p.1 ∈ S ω ∧ p.2 ∈ T ω ∧
      dist (p.1 + p.2) (h ω) = infDist (h ω) (S ω + T ω) := by
  have hp := (kuratowski_ryll_nardzewski
    (effrosMeasurable_minkowskiDecompositionArgmin
      hS hT hScompact hTcompact hSne hTne hh)
    (fun ω =>
      (minkowskiDecompositionArgmin_isCompact hScompact hTcompact h ω).isClosed)
    (minkowskiDecompositionArgmin_nonempty
      hScompact hTcompact hSne hTne h)).2 ω
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

/-- A measurable selection of a pointwise Minkowski sum admits two globally
measurable coordinate selections whose sum is the target pointwise.-/
theorem exists_measurable_minkowski_decomposition
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h)
    (hhmem : ∀ ω, h ω ∈ S ω + T ω) :
    ∃ f g : Ω → E,
      Measurable f ∧ Measurable g ∧
        (∀ ω, f ω ∈ S ω) ∧ (∀ ω, g ω ∈ T ω) ∧
          ∀ ω, h ω = f ω + g ω := by
  let p := minkowskiDecompositionSelection
    hS hT hScompact hTcompact hSne hTne hh
  have hpmeas : Measurable p :=
    measurable_minkowskiDecompositionSelection
      hS hT hScompact hTcompact hSne hTne hh
  have hpprop := minkowskiDecompositionSelection_mem_and_residual_eq
    hS hT hScompact hTcompact hSne hTne hh
  refine ⟨fun ω => (p ω).1, fun ω => (p ω).2,
    hpmeas.fst, hpmeas.snd, ?_, ?_, ?_⟩
  · exact fun ω => (hpprop ω).1
  · exact fun ω => (hpprop ω).2.1
  · intro ω
    have hdist : dist ((p ω).1 + (p ω).2) (h ω) = 0 :=
      (hpprop ω).2.2.trans (infDist_zero_of_mem (hhmem ω))
    exact (dist_eq_zero.mp hdist).symm

/-- Almost-everywhere membership in the sum suffices for an almost-everywhere
exact decomposition; the coordinate selections still belong to their fibres
at every base point.-/
theorem exists_measurable_minkowski_decomposition_ae
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {h : Ω → E} (hh : Measurable h)
    (hhmem : ∀ᵐ ω ∂μ, h ω ∈ S ω + T ω) :
    ∃ f g : Ω → E,
      Measurable f ∧ Measurable g ∧
        (∀ ω, f ω ∈ S ω) ∧ (∀ ω, g ω ∈ T ω) ∧
          h =ᵐ[μ] fun ω => f ω + g ω := by
  let p := minkowskiDecompositionSelection
    hS hT hScompact hTcompact hSne hTne hh
  have hpmeas : Measurable p :=
    measurable_minkowskiDecompositionSelection
      hS hT hScompact hTcompact hSne hTne hh
  have hpprop := minkowskiDecompositionSelection_mem_and_residual_eq
    hS hT hScompact hTcompact hSne hTne hh
  refine ⟨fun ω => (p ω).1, fun ω => (p ω).2,
    hpmeas.fst, hpmeas.snd, ?_, ?_, ?_⟩
  · exact fun ω => (hpprop ω).1
  · exact fun ω => (hpprop ω).2.1
  · filter_upwards [hhmem] with ω hω
    have hdist : dist ((p ω).1 + (p ω).2) (h ω) = 0 :=
      (hpprop ω).2.2.trans (infDist_zero_of_mem hω)
    exact (dist_eq_zero.mp hdist).symm

/-- Compact nonempty Effros-measurable summands with integrable envelopes
have the integrable Minkowski decomposition property required by the Aumann
expectation API.-/
theorem hasIntegrableMinkowskiDecomposition_of_effros_of_envelopes
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {gS gT : Ω → ℝ} (hgS : Integrable gS μ) (hgT : Integrable gT μ)
    (hdomS : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ gS ω)
    (hdomT : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ gT ω) :
    HasIntegrableMinkowskiDecomposition μ S T := by
  intro h hh
  let h' : Ω → E := hh.1.aestronglyMeasurable.mk h
  have hh'meas : Measurable h' :=
    hh.1.aestronglyMeasurable.measurable_mk
  have hheq : h =ᵐ[μ] h' :=
    hh.1.aestronglyMeasurable.ae_eq_mk
  have hh'mem : ∀ᵐ ω ∂μ, h' ω ∈ S ω + T ω := by
    filter_upwards [hh.2, hheq] with ω hmem heq
    rw [← heq]
    exact hmem
  obtain ⟨f, g, hfmeas, hgmeas, hfmem, hgmem, hsum⟩ :=
    exists_measurable_minkowski_decomposition_ae
      hS hT hScompact hTcompact hSne hTne hh'meas hh'mem
  have hfint : Integrable f μ := by
    apply hgS.mono' hfmeas.aestronglyMeasurable
    filter_upwards [] with ω
    exact hdomS ω (f ω) (hfmem ω)
  have hgint : Integrable g μ := by
    apply hgT.mono' hgmeas.aestronglyMeasurable
    filter_upwards [] with ω
    exact hdomT ω (g ω) (hgmem ω)
  exact ⟨f, g,
    ⟨hfint, Filter.Eventually.of_forall hfmem⟩,
    ⟨hgint, Filter.Eventually.of_forall hgmem⟩,
    hheq.trans hsum⟩

/-- Under the same concrete random-set hypotheses, Aumann expectation is
Minkowski additive with no separate decomposition axiom.-/
theorem aumannExpectation_add_of_effros_of_envelopes
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty)
    {gS gT : Ω → ℝ} (hgS : Integrable gS μ) (hgT : Integrable gT μ)
    (hdomS : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ gS ω)
    (hdomT : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ gT ω) :
    aumannExpectation μ (fun ω => S ω + T ω) =
      aumannExpectation μ S + aumannExpectation μ T :=
  aumannExpectation_add
    (hasIntegrableMinkowskiDecomposition_of_effros_of_envelopes
      hS hT hScompact hTcompact hSne hTne hgS hgT hdomS hdomT)

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
