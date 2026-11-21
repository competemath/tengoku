/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Approximate measurable selections

An Effros-measurable nonempty correspondence into a separable metric space
admits measurable selections at every positive accuracy.  The construction
chooses the first element of a fixed dense sequence whose open ball hits the
current value.  This is the first constructive step of the
Kuratowski--Ryll-Nardzewski theorem.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace Filter
open scoped Topology

noncomputable section

namespace RandomSetTheory

/-- A globally measurable selection of a correspondence.-/
def IsMeasurableSelection {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (S : Ω → Set E) (f : Ω → E) : Prop :=
  Measurable f ∧ ∀ ω, f ω ∈ S ω

/-- The `n`th point of the canonical dense sequence is an `ε`-candidate when
its ball hits the value of the correspondence.-/
def DenseHit {Ω E : Type*} [PseudoMetricSpace E] [SeparableSpace E] [Nonempty E]
    (S : Ω → Set E) (ε : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  (S ω ∩ Metric.ball (denseSeq E n) ε).Nonempty

/--
@isnad1 id=ex.2h5v.s5.a2f712e4fde3 from=translated src=- shape=9b865f10 vocab=e901cb1a
-/
theorem exists_denseHit
    {Ω E : Type*} [PseudoMetricSpace E] [SeparableSpace E] [Nonempty E]
    (S : Ω → Set E) (hne : ∀ ω, (S ω).Nonempty)
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    ∃ n, DenseHit S ε n ω := by
  obtain ⟨x, hx⟩ := hne ω
  obtain ⟨n, hxn⟩ := (denseRange_denseSeq E).exists_dist_lt x hε
  refine ⟨n, x, hx, ?_⟩
  simpa [DenseHit, Metric.mem_ball, dist_comm] using hxn

/-- Canonical measurable `ε`-selection obtained by the first-hit rule on a
dense sequence.-/
def effrosApproximateSelection
    {Ω E : Type*} [PseudoMetricSpace E] [SeparableSpace E] [Nonempty E]
    (S : Ω → Set E) (hne : ∀ ω, (S ω).Nonempty)
    (ε : ℝ) (hε : 0 < ε) (ω : Ω) : E := by
  classical
  exact denseSeq E (Nat.find (exists_denseHit S hne hε ω))

/-- A function only takes values in the canonical dense sequence.-/
def IsDenseSeqValued {Ω E : Type*} [TopologicalSpace E]
    [SeparableSpace E] [Nonempty E] (f : Ω → E) : Prop :=
  ∀ ω, ∃ n, f ω = denseSeq E n

/--
@isnad1 id=isdenses.2h4v.s6.c02610d2d484 from=translated src=- shape=2c4cdc65 vocab=30a17d0d
-/
theorem isDenseSeqValued_effrosApproximateSelection
    {Ω E : Type*} [PseudoMetricSpace E] [SeparableSpace E] [Nonempty E]
    (S : Ω → Set E) (hne : ∀ ω, (S ω).Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    IsDenseSeqValued (effrosApproximateSelection S hne ε hε) := by
  classical
  intro ω
  exact ⟨Nat.find (exists_denseHit S hne hε ω), rfl⟩

/--
@isnad1 id=measurab.3h4v.s6.08831f0f56b1 from=translated src=- shape=3e1914c7 vocab=b71d4cf9
-/
theorem measurable_effrosApproximateSelection
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    Measurable (effrosApproximateSelection S hne ε hε) := by
  classical
  exact Measurable.find
    (p := fun n ω => DenseHit S ε n ω)
    (f := fun n _ => denseSeq E n)
    (fun _ => measurable_const)
    (fun n => by
      simpa [DenseHit] using
        hS (Metric.ball (denseSeq E n) ε) Metric.isOpen_ball)
    (exists_denseHit S hne hε)

/--
@isnad1 id=lt.2h5v.s6.df584002ebb9 from=translated src=- shape=df66b4b5 vocab=c721534f
-/
theorem infDist_effrosApproximateSelection_lt
    {Ω E : Type*} [PseudoMetricSpace E] [SeparableSpace E] [Nonempty E]
    (S : Ω → Set E) (hne : ∀ ω, (S ω).Nonempty)
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    infDist (effrosApproximateSelection S hne ε hε ω) (S ω) < ε := by
  classical
  have hhit := Nat.find_spec (exists_denseHit S hne hε ω)
  rcases hhit with ⟨x, hx, hxball⟩
  apply (infDist_le_dist_of_mem hx).trans_lt
  simpa [effrosApproximateSelection, DenseHit, Metric.mem_ball, dist_comm] using hxball

/-- Intersecting an Effros-measurable correspondence with a moving open ball
preserves Effros measurability when the measurable center is countably valued
in the canonical dense sequence.
@isnad1 id=iseffros.3h5v.s6.026cc43c493c from=translated src=- shape=fc492b6f vocab=337870ff
-/
theorem RandomSet.IsEffrosMeasurable.inter_ball_of_isDenseSeqValued
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    {f : Ω → E} (hf : Measurable f) (hfdense : IsDenseSeqValued f)
    (r : ℝ) :
    RandomSet.IsEffrosMeasurable (fun ω => S ω ∩ Metric.ball (f ω) r) := by
  intro U hU
  have hEq : {ω | ((S ω ∩ Metric.ball (f ω) r) ∩ U).Nonempty} =
      ⋃ n : ℕ, (f ⁻¹' ({denseSeq E n} : Set E)) ∩
        {ω | (S ω ∩ (Metric.ball (denseSeq E n) r ∩ U)).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxS, hxball⟩, hxU⟩
      obtain ⟨n, hn⟩ := hfdense ω
      refine ⟨n, hn, x, hxS, ?_, hxU⟩
      simpa [hn] using hxball
    · rintro ⟨n, hfn, x, hxS, hxball, hxU⟩
      refine ⟨x, ⟨hxS, ?_⟩, hxU⟩
      simpa [hfn] using hxball
  rw [hEq]
  apply MeasurableSet.iUnion
  intro n
  exact (hf (measurableSet_singleton (denseSeq E n))).inter
    (hS (Metric.ball (denseSeq E n) r ∩ U) (Metric.isOpen_ball.inter hU))

/--
@isnad1 id=nonempty.2h6v.s5.065cac2885cb from=translated src=- shape=e3fb2046 vocab=01e417d7
-/
theorem nonempty_inter_ball_of_infDist_lt
    {Ω E : Type*} [PseudoMetricSpace E]
    {S : Ω → Set E} (hne : ∀ ω, (S ω).Nonempty)
    {f : Ω → E} {r : ℝ}
    (hclose : ∀ ω, infDist (f ω) (S ω) < r) (ω : Ω) :
    (S ω ∩ Metric.ball (f ω) r).Nonempty := by
  obtain ⟨x, hx, hdist⟩ := (infDist_lt_iff (hne ω)).mp (hclose ω)
  exact ⟨x, hx, by simpa [Metric.mem_ball, dist_comm] using hdist⟩

/-- Packaged approximate measurable selection theorem.
@isnad1 id=ex.3h4v.s6.5c0082c97afe from=translated src=- shape=4b9ccc5b vocab=9aec1f43
-/
theorem exists_measurable_infDist_lt
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Ω → E, Measurable f ∧ ∀ ω, infDist (f ω) (S ω) < ε := by
  exact ⟨effrosApproximateSelection S hne ε hε,
    measurable_effrosApproximateSelection hS hne hε,
    infDist_effrosApproximateSelection_lt S hne hε⟩

/-- Limit criterion for an exact measurable selection: measurable
approximations converging pointwise to `f`, with distance to the closed values
tending to zero, force `f(ω) ∈ S(ω)`.
@isnad1 id=ismeasur.5h5v.s7.d8d264702789 from=translated src=- shape=83dba372 vocab=6649d4db
-/
theorem isMeasurableSelection_of_tendsto_infDist_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {S : Ω → Set E} (hclosed : ∀ ω, IsClosed (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {f : ℕ → Ω → E} {g : Ω → E}
    (hf : ∀ n, Measurable (f n))
    (hfg : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hdist : ∀ ω,
      Tendsto (fun n => infDist (f n ω) (S ω)) atTop (𝓝 0)) :
    IsMeasurableSelection S g := by
  constructor
  · apply measurable_of_tendsto_metrizable hf
    rw [tendsto_pi_nhds]
    exact hfg
  · intro ω
    apply ((hclosed ω).mem_iff_infDist_zero (hne ω)).mpr
    have hcont : Tendsto (fun n => infDist (f n ω) (S ω)) atTop
        (𝓝 (infDist (g ω) (S ω))) :=
      (continuous_infDist_pt (S ω)).tendsto (g ω) |>.comp (hfg ω)
    exact tendsto_nhds_unique hcont (hdist ω)

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
