/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosOperations
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableHausdorff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable size functionals of random compact sets

This file supplies canonical scalar size functionals for an
Effros-measurable compact random set.  The radius about a point is the
supremum of the distances to that point.  On a nonempty compact set it is
also the Hausdorff distance to the corresponding singleton, which proves
measurability even when the centre depends measurably on the outcome.

The diameter admits a second, slightly stronger result.  A Castaing
representation turns the extended diameter into a double countable
supremum of pairwise distances.  Thus both `Metric.ediam` and
`Metric.diam` are measurable already for nonempty closed-valued Effros
correspondences.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace

noncomputable section

namespace RandomSetTheory

/-! ## Radius about a point -/

/-- The radius of `K` about `x₀`: the supremum of the distances from
points of `K` to `x₀`.  The compact nonempty hypotheses used below make
this supremum finite and attained.-/
def setRadiusAt {E : Type*} [PseudoMetricSpace E] (K : Set E) (x₀ : E) : ℝ :=
  sSup ((fun x => dist x x₀) '' K)

/-- Every point of a compact set lies within its radius about `x₀`.-/
theorem dist_le_setRadiusAt
    {E : Type*} [PseudoMetricSpace E] {K : Set E} {x x₀ : E}
    (hcompact : IsCompact K) (hx : x ∈ K) :
    dist x x₀ ≤ setRadiusAt K x₀ := by
  apply le_csSup
  · exact (hcompact.image (continuous_id.dist continuous_const)).bddAbove
  · exact ⟨x, hx, rfl⟩

/-- The radius of a nonempty compact set is nonnegative.-/
theorem setRadiusAt_nonneg
    {E : Type*} [PseudoMetricSpace E] {K : Set E} {x₀ : E}
    (hcompact : IsCompact K) (hne : K.Nonempty) :
    0 ≤ setRadiusAt K x₀ := by
  obtain ⟨x, hx⟩ := hne
  exact dist_nonneg.trans (dist_le_setRadiusAt hcompact hx)

/-- The radius of a nonempty compact set is attained.-/
theorem exists_mem_setRadiusAt_eq_dist
    {E : Type*} [PseudoMetricSpace E] {K : Set E} {x₀ : E}
    (hcompact : IsCompact K) (hne : K.Nonempty) :
    ∃ x ∈ K, setRadiusAt K x₀ = dist x x₀ := by
  obtain ⟨x, hx, heq, _⟩ := hcompact.exists_sSup_image_eq_and_ge hne
    (continuous_id.dist continuous_const).continuousOn
  exact ⟨x, hx, heq⟩

/-- For a nonempty compact set, the radius about `x₀` is exactly its
Hausdorff distance to the singleton `{x₀}`.-/
theorem setRadiusAt_eq_hausdorffDist_singleton
    {E : Type*} [PseudoMetricSpace E] {K : Set E} {x₀ : E}
    (hcompact : IsCompact K) (hne : K.Nonempty) :
    setRadiusAt K x₀ = hausdorffDist K {x₀} := by
  apply le_antisymm
  · obtain ⟨x, hx, hradius⟩ :=
      exists_mem_setRadiusAt_eq_dist hcompact hne
    have hfin : hausdorffEDist K {x₀} ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded hne
        (singleton_nonempty x₀) hcompact.isBounded
        Bornology.isBounded_singleton
    calc
      setRadiusAt K x₀ = dist x x₀ := hradius
      _ = infDist x {x₀} := infDist_singleton.symm
      _ ≤ hausdorffDist K {x₀} :=
        infDist_le_hausdorffDist_of_mem hx hfin
  · apply hausdorffDist_le_of_mem_dist
      (setRadiusAt_nonneg hcompact hne)
    · intro x hx
      exact ⟨x₀, mem_singleton x₀,
        dist_le_setRadiusAt hcompact hx⟩
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, by
        simpa only [dist_comm] using
          (dist_le_setRadiusAt (x₀ := x₀) hcompact hy)⟩

/-- The radius about a measurably varying centre is measurable.-/
theorem measurable_setRadiusAt
    {Omega E : Type*} [MeasurableSpace Omega]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty)
    {c : Omega → E} (hc : Measurable c) :
    Measurable (fun omega => setRadiusAt (S omega) (c omega)) := by
  have hsingleton : RandomSet.IsEffrosMeasurable
      (fun omega => ({c omega} : Set E)) :=
    RandomSet.isEffrosMeasurable_singleton hc
  have hhausdorff : Measurable
      (fun omega => hausdorffDist (S omega) ({c omega} : Set E)) :=
    measurable_hausdorffDist_correspondence hS hsingleton
      (fun omega => (hcompact omega).isClosed)
      (fun _ => isClosed_singleton)
      hne (fun omega => singleton_nonempty (c omega))
  have heq : (fun omega => setRadiusAt (S omega) (c omega)) =
      fun omega => hausdorffDist (S omega) ({c omega} : Set E) := by
    funext omega
    exact setRadiusAt_eq_hausdorffDist_singleton
      (hcompact omega) (hne omega)
  rw [heq]
  exact hhausdorff

/-- In particular, the radius about a fixed deterministic point is
measurable.-/
theorem measurable_setRadiusAt_const
    {Omega E : Type*} [MeasurableSpace Omega]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty) (x₀ : E) :
    Measurable (fun omega => setRadiusAt (S omega) x₀) := by
  exact measurable_setRadiusAt hS hcompact hne measurable_const

/-! ## Diameter and radius bounds -/

/-- The diameter of a compact set is at most twice its radius about any
point.-/
theorem diam_le_two_mul_setRadiusAt
    {E : Type*} [PseudoMetricSpace E] {K : Set E} {x₀ : E}
    (hcompact : IsCompact K) (hne : K.Nonempty) :
    Metric.diam K ≤ 2 * setRadiusAt K x₀ := by
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg zero_le_two (setRadiusAt_nonneg hcompact hne))
  intro x hx y hy
  calc
    dist x y ≤ dist x x₀ + dist y x₀ := dist_triangle_right x y x₀
    _ ≤ setRadiusAt K x₀ + setRadiusAt K x₀ :=
      add_le_add (dist_le_setRadiusAt hcompact hx)
        (dist_le_setRadiusAt hcompact hy)
    _ = 2 * setRadiusAt K x₀ := by ring

/-- If the centre belongs to the set, its radius is bounded by the
diameter.-/
theorem setRadiusAt_le_diam_of_mem
    {E : Type*} [PseudoMetricSpace E] {K : Set E} {x₀ : E}
    (hcompact : IsCompact K) (hx₀ : x₀ ∈ K) :
    setRadiusAt K x₀ ≤ Metric.diam K := by
  apply csSup_le
  · exact ⟨dist x₀ x₀, ⟨x₀, hx₀, rfl⟩⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact Metric.dist_le_diam_of_mem hcompact.isBounded hx hx₀

/-! ## Measurability of the diameter -/

/-- A Castaing representation computes the extended diameter as a double
countable supremum of pairwise extended distances.-/
theorem ediam_eq_iSup_edist_castaingRepresentation
    {Omega E : Type*} [MeasurableSpace Omega]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ omega, IsClosed (S omega))
    (hne : ∀ omega, (S omega).Nonempty) (omega : Omega) :
    Metric.ediam (S omega) =
      ⨆ i : ℕ, ⨆ j : ℕ,
        edist (castaingRepresentation hS hclosed hne i omega)
          (castaingRepresentation hS hclosed hne j omega) := by
  let f : ℕ → Omega → E := castaingRepresentation hS hclosed hne
  calc
    Metric.ediam (S omega) =
        Metric.ediam (closure (Set.range fun n => f n omega)) := by
      rw [closure_range_castaingRepresentation hS hclosed hne omega]
    _ = Metric.ediam (Set.range fun n => f n omega) :=
      Metric.ediam_closure _
    _ = ⨆ i : ℕ, ⨆ j : ℕ, edist (f i omega) (f j omega) := by
      simp only [Metric.ediam, iSup_range]
    _ = ⨆ i : ℕ, ⨆ j : ℕ,
        edist (castaingRepresentation hS hclosed hne i omega)
          (castaingRepresentation hS hclosed hne j omega) := rfl

/-- The extended diameter of a nonempty closed-valued Effros
correspondence is measurable.-/
theorem measurable_ediam_correspondence
    {Omega E : Type*} [MeasurableSpace Omega]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ omega, IsClosed (S omega))
    (hne : ∀ omega, (S omega).Nonempty) :
    Measurable (fun omega => Metric.ediam (S omega)) := by
  let f : ℕ → Omega → E := castaingRepresentation hS hclosed hne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hS hclosed hne
  have heq : (fun omega => Metric.ediam (S omega)) =
      fun omega => ⨆ i : ℕ, ⨆ j : ℕ, edist (f i omega) (f j omega) := by
    funext omega
    exact ediam_eq_iSup_edist_castaingRepresentation
      hS hclosed hne omega
  rw [heq]
  exact Measurable.iSup fun i => Measurable.iSup fun j =>
    (hf i).edist (hf j)

/-- The ordinary real diameter is measurable.  For compact fibres this is
the usual finite diameter; the statement remains valid for arbitrary
nonempty closed fibres because `Metric.diam` is defined as
`ENNReal.toReal Metric.ediam`.-/
theorem measurable_diam_correspondence
    {Omega E : Type*} [MeasurableSpace Omega]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ omega, IsClosed (S omega))
    (hne : ∀ omega, (S omega).Nonempty) :
    Measurable (fun omega => Metric.diam (S omega)) := by
  exact (measurable_ediam_correspondence hS hclosed hne).ennreal_toReal

/-- Compact-valued specialization of diameter measurability.-/
theorem measurable_diam_compact_correspondence
    {Omega E : Type*} [MeasurableSpace Omega]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty) :
    Measurable (fun omega => Metric.diam (S omega)) :=
  measurable_diam_correspondence hS (fun omega => (hcompact omega).isClosed) hne

/-! ## Canonical norm envelope -/

/-- The canonical norm envelope of a set in a normed group.-/
def setNormEnvelope {E : Type*} [SeminormedAddCommGroup E] (K : Set E) : ℝ :=
  setRadiusAt K 0

theorem setNormEnvelope_eq_sSup_norm
    {E : Type*} [SeminormedAddCommGroup E] (K : Set E) :
    setNormEnvelope K = sSup ((fun x => ‖x‖) '' K) := by
  simp only [setNormEnvelope, setRadiusAt, dist_zero_right]

theorem norm_le_setNormEnvelope
    {E : Type*} [SeminormedAddCommGroup E] {K : Set E} {x : E}
    (hcompact : IsCompact K) (hx : x ∈ K) :
    ‖x‖ ≤ setNormEnvelope K := by
  simpa only [setNormEnvelope, dist_zero_right] using
    (dist_le_setRadiusAt hcompact hx : dist x 0 ≤ setRadiusAt K 0)

theorem measurable_setNormEnvelope
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty) :
    Measurable (fun omega => setNormEnvelope (S omega)) := by
  exact measurable_setRadiusAt_const hS hcompact hne 0

theorem diam_le_two_mul_setNormEnvelope
    {E : Type*} [NormedAddCommGroup E] {K : Set E}
    (hcompact : IsCompact K) (hne : K.Nonempty) :
    Metric.diam K ≤ 2 * setNormEnvelope K := by
  exact diam_le_two_mul_setRadiusAt hcompact hne

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
