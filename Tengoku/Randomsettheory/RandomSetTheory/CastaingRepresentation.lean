/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.KuratowskiRyllNardzewski
import Tengoku.Seed.Data.Nat.Pairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Castaing representation of a random closed set

We localize a closed-valued Effros-measurable correspondence in the balls of
a fixed dense sequence.  The localization is closed by taking a closure and
falls back to the original value when the ball is missed.  Applying the
Kuratowski--Ryll-Nardzewski theorem to all localizations gives a countable
family of measurable selections whose values are dense in every fibre.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace Filter
open scoped Topology

noncomputable section

namespace RandomSetTheory

/-- A closed localization of `S` in an open ball.  If the ball misses the
current fibre, the original fibre is used so that values stay nonempty.-/
def castaingLocalization {Ω E : Type*} [PseudoMetricSpace E]
    (S : Ω → Set E) (q : E) (r : ℝ) (ω : Ω) : Set E := by
  classical
  exact if (S ω ∩ Metric.ball q r).Nonempty then
      closure (S ω ∩ Metric.ball q r)
    else S ω

theorem castaingLocalization_isClosed
    {Ω E : Type*} [PseudoMetricSpace E]
    {S : Ω → Set E} (hclosed : ∀ ω, IsClosed (S ω))
    (q : E) (r : ℝ) (ω : Ω) :
    IsClosed (castaingLocalization S q r ω) := by
  classical
  by_cases hhit : (S ω ∩ Metric.ball q r).Nonempty
  · rw [castaingLocalization, ite_eq_left hhit]
    exact isClosed_closure
  · simpa [castaingLocalization, hhit] using hclosed ω

theorem castaingLocalization_nonempty
    {Ω E : Type*} [PseudoMetricSpace E]
    {S : Ω → Set E} (hne : ∀ ω, (S ω).Nonempty)
    (q : E) (r : ℝ) (ω : Ω) :
    (castaingLocalization S q r ω).Nonempty := by
  classical
  by_cases hhit : (S ω ∩ Metric.ball q r).Nonempty
  · rw [castaingLocalization, ite_eq_left hhit]
    exact hhit.closure
  · simpa [castaingLocalization, hhit] using hne ω

theorem castaingLocalization_isCompact
    {Ω E : Type*} [MetricSpace E]
    {S : Ω → Set E} (hcompact : ∀ ω, IsCompact (S ω))
    (q : E) (r : ℝ) (ω : Ω) :
    IsCompact (castaingLocalization S q r ω) := by
  classical
  by_cases hhit : (S ω ∩ Metric.ball q r).Nonempty
  · rw [castaingLocalization, ite_eq_left hhit]
    exact IsCompact.of_isClosed_subset (hcompact ω) isClosed_closure
      (closure_minimal inter_subset_left (hcompact ω).isClosed)
  · simpa [castaingLocalization, hhit] using hcompact ω

theorem castaingLocalization_subset
    {Ω E : Type*} [PseudoMetricSpace E]
    {S : Ω → Set E} (hclosed : ∀ ω, IsClosed (S ω))
    (q : E) (r : ℝ) (ω : Ω) :
    castaingLocalization S q r ω ⊆ S ω := by
  classical
  by_cases hhit : (S ω ∩ Metric.ball q r).Nonempty
  · rw [castaingLocalization, ite_eq_left hhit]
    exact closure_minimal inter_subset_left (hclosed ω)
  · simp [castaingLocalization, hhit]

/-- Closed localization preserves Effros measurability.-/
theorem effros_castaingLocalization
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (q : E) (r : ℝ) :
    RandomSet.IsEffrosMeasurable (castaingLocalization S q r) := by
  classical
  intro U hU
  let A : Set Ω := {ω | (S ω ∩ Metric.ball q r).Nonempty}
  have hA : MeasurableSet A := hS (Metric.ball q r) Metric.isOpen_ball
  have hEq :
      {ω | (castaingLocalization S q r ω ∩ U).Nonempty} =
        (A ∩ {ω | (S ω ∩ (Metric.ball q r ∩ U)).Nonempty}) ∪
          (Aᶜ ∩ {ω | (S ω ∩ U).Nonempty}) := by
    ext ω
    by_cases hhit : (S ω ∩ Metric.ball q r).Nonempty
    · simp [A, castaingLocalization, hhit,
        closure_inter_open_nonempty_iff hU, inter_assoc]
    · simp [A, castaingLocalization, hhit]
  rw [hEq]
  exact (hA.inter
      (hS (Metric.ball q r ∩ U) (Metric.isOpen_ball.inter hU))).union
    (hA.compl.inter (hS U hU))

/-- The localized measurable selection indexed by a dense point and an
inverse-natural radius.-/
def castaingLocalSelection
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (_hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (k m : ℕ) : Ω → E :=
  krnSelection
    (effros_castaingLocalization hS (denseSeq E k) (1 / (m + 1 : ℝ)))
    (castaingLocalization_nonempty hne (denseSeq E k) (1 / (m + 1 : ℝ)))

/-- Flatten the two localization indices using the canonical pairing
equivalence on natural numbers.-/
def castaingRepresentation
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (n : ℕ) : Ω → E :=
  let p := Nat.unpair n
  castaingLocalSelection hS hclosed hne p.1 p.2

theorem castaingRepresentation_measurable
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (n : ℕ) : Measurable (castaingRepresentation hS hclosed hne n) := by
  let p := Nat.unpair n
  exact (kuratowski_ryll_nardzewski
    (effros_castaingLocalization hS (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)))
    (castaingLocalization_isClosed hclosed
      (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)))
    (castaingLocalization_nonempty hne
      (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)))).1

theorem castaingRepresentation_mem
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (n : ℕ) (ω : Ω) : castaingRepresentation hS hclosed hne n ω ∈ S ω := by
  let p := Nat.unpair n
  have hloc := (kuratowski_ryll_nardzewski
    (effros_castaingLocalization hS (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)))
    (castaingLocalization_isClosed hclosed
      (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)))
    (castaingLocalization_nonempty hne
      (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)))).2 ω
  exact castaingLocalization_subset hclosed
    (denseSeq E p.1) (1 / (p.2 + 1 : ℝ)) ω hloc

/-- **Castaing representation theorem**: the values of the canonical sequence
of measurable selections are dense in each closed fibre.-/
theorem closure_range_castaingRepresentation
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (ω : Ω) :
    closure (Set.range fun n => castaingRepresentation hS hclosed hne n ω) = S ω := by
  apply Subset.antisymm
  · apply closure_minimal _ (hclosed ω)
    rintro _ ⟨n, rfl⟩
    exact castaingRepresentation_mem hS hclosed hne n ω
  · intro x hx
    rw [Metric.mem_closure_range_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
    let r : ℝ := 1 / (m + 1 : ℝ)
    have hr : 0 < r := by positivity
    obtain ⟨k, hk⟩ := (denseRange_denseSeq E).exists_dist_lt x hr
    let n := Nat.pair k m
    refine ⟨n, ?_⟩
    have hhit : (S ω ∩ Metric.ball (denseSeq E k) r).Nonempty := by
      refine ⟨x, hx, ?_⟩
      simpa [Metric.mem_ball, dist_comm] using hk
    have hzloc := (kuratowski_ryll_nardzewski
      (effros_castaingLocalization hS (denseSeq E k) r)
      (castaingLocalization_isClosed hclosed (denseSeq E k) r)
      (castaingLocalization_nonempty hne (denseSeq E k) r)).2 ω
    have hzloc' :
        krnSelection
            (effros_castaingLocalization hS (denseSeq E k) r)
            (castaingLocalization_nonempty hne (denseSeq E k) r) ω ∈
          closure (S ω ∩ Metric.ball (denseSeq E k) r) := by
      rw [castaingLocalization, ite_eq_left hhit] at hzloc
      exact hzloc
    have hzclosure :
        castaingLocalSelection hS hclosed hne k m ω ∈
          closure (S ω ∩ Metric.ball (denseSeq E k) r) := by
      simpa [castaingLocalSelection, r] using hzloc'
    have hzball :
        castaingLocalSelection hS hclosed hne k m ω ∈
          Metric.closedBall (denseSeq E k) r :=
      closure_minimal
        (inter_subset_right.trans Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall hzclosure
    have hrepr :
        castaingRepresentation hS hclosed hne n ω =
          castaingLocalSelection hS hclosed hne k m ω := by
      simp [n, castaingRepresentation]
    rw [hrepr]
    calc
      dist x (castaingLocalSelection hS hclosed hne k m ω) ≤
          dist x (denseSeq E k) +
            dist (denseSeq E k) (castaingLocalSelection hS hclosed hne k m ω) :=
        dist_triangle _ _ _
      _ < r + r := add_lt_add_of_lt_of_le hk
        (by simpa [Metric.mem_closedBall, dist_comm] using hzball)
      _ < ε := by
        dsimp [r] at hm ⊢
        linarith

/-- Existential form of the Castaing representation theorem.-/
theorem exists_castaingRepresentation
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty) :
    ∃ f : ℕ → Ω → E,
      (∀ n, Measurable (f n)) ∧
        (∀ n ω, f n ω ∈ S ω) ∧
          ∀ ω, closure (Set.range fun n => f n ω) = S ω := by
  exact ⟨castaingRepresentation hS hclosed hne,
    castaingRepresentation_measurable hS hclosed hne,
    castaingRepresentation_mem hS hclosed hne,
    closure_range_castaingRepresentation hS hclosed hne⟩

/-- Conversely, a fibrewise dense countable family of measurable functions
makes the correspondence Effros measurable.-/
theorem effrosMeasurable_of_closure_range
    {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {S : Ω → Set E} {f : ℕ → Ω → E}
    (hf : ∀ n, Measurable (f n))
    (hclosure : ∀ ω, closure (Set.range fun n => f n ω) = S ω) :
    RandomSet.IsEffrosMeasurable S := by
  intro U hU
  have hEq : {ω | (S ω ∩ U).Nonempty} = ⋃ n : ℕ, f n ⁻¹' U := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [← hclosure ω, closure_inter_open_nonempty_iff hU]
    constructor
    · rintro ⟨x, ⟨n, rfl⟩, hUmem⟩
      exact ⟨n, hUmem⟩
    · rintro ⟨n, hn⟩
      exact ⟨f n ω, ⟨n, rfl⟩, hn⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun n => hf n hU.measurableSet

/-- Castaing's characterization of nonempty random closed sets.-/
theorem effrosMeasurable_iff_exists_castaing
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hclosed : ∀ ω, IsClosed (S ω))
    (hne : ∀ ω, (S ω).Nonempty) :
    RandomSet.IsEffrosMeasurable S ↔
      ∃ f : ℕ → Ω → E,
        (∀ n, Measurable (f n)) ∧
          (∀ n ω, f n ω ∈ S ω) ∧
            ∀ ω, closure (Set.range fun n => f n ω) = S ω := by
  constructor
  · intro hS
    exact exists_castaingRepresentation hS hclosed hne
  · rintro ⟨f, hf, -, hclosure⟩
    exact effrosMeasurable_of_closure_range hf hclosure

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
