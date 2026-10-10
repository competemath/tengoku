import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.CauchyApproximation

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

structure CauchyLocalizationState (R : ℝ≥0) where
  seq : ℕ → Space M
  weak : WeakSequences.WeakCauchy seq
  set : Set M
  closed : IsClosed set
  zero_mem : (0 : M) ∈ set
  bounded : set ⊆ Metric.closedBall 0 (R : ℝ)
  support : ∀ i, seq i ∈ supported set

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weakCauchy_biddual_limit {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
      ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)) := by
  classical
  choose a ha using fun f : E →L[ℝ] ℝ => cauchySeq_tendsto_of_complete (hu f)
  let L : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ := {
    toFun := a
    map_add' := fun f g => tendsto_nhds_unique (ha (f+g)) ((ha f).add (ha g))
    map_smul' := fun c f => tendsto_nhds_unique (ha (c • f)) ((ha f).const_smul c) }
  obtain ⟨C,hC⟩ := hu.bounded
  have hbound (f : E →L[ℝ] ℝ) : ‖L f‖ ≤ C*‖f‖ := by
    apply le_of_tendsto (ha f).norm
    apply Eventually.of_forall
    intro n
    exact (f.le_opNorm (u n)).trans (by nlinarith [norm_nonneg f,hC n])
  exact ⟨L.mkContinuous C hbound,ha⟩

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.FreeSpace
open Filter Topology
variable {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]

end LipschitzCounterexample.FreeSpace

end

end OAI
