/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.IidConcentration
import Tengoku.Seed.MeasureTheory.Covering.BesicovitchVectorSpace
import Tengoku.Seed.Topology.MetricSpace.CoveringNumbers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Volumetric cardinality of Euclidean nets

This file proves the standard volumetric estimate for a finite net of the
unit ball of a finite-dimensional real normed space.  A maximal separated
set supplies centres inside the ball and the covering property; disjoint
small balls and Haar measure give the cardinality estimate

`card N ≤ (1 + 2 / ε) ^ finrank ℝ E`.

The last theorems insert this estimate into the iid random-set concentration
bound, producing the explicit dimension-dependent factor used in the report.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Real Set Metric Finset MeasureTheory Module ProbabilityTheory
open scoped ENNReal NNReal Pointwise BigOperators InnerProductSpace ProbabilityTheory

noncomputable section

namespace RandomSetTheory

section VolumetricPacking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Volumetric packing inequality in `ℝ≥0∞`.  Writing it before cancelling
the unit-ball volume avoids any division by extended-real quantities.-/
theorem finset_card_mul_ballVolume_le
    (s : Finset E) {R eps : ℝ} (heps : 0 < eps)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → eps ≤ ‖c - d‖) :
    (s.card : ℝ≥0∞) * ENNReal.ofReal ((eps / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + eps / 2) ^ finrank ℝ E) := by
  classical
  by_cases hs0 : s = ∅
  · subst s
    simp
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := eps / 2
  let ρ : ℝ := R + eps / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hR : 0 ≤ R := by
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    exact (norm_nonneg c).trans (hs c hc)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hdisj : Set.Pairwise (s : Set E)
      (fun c d => Disjoint (ball (c : E) δ) (ball (d : E) δ)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have hcd' := hsep c hc d hd hcd
    dsimp [δ]
    linarith
  have hsubset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + R := by
        simpa only [dist_zero_right, add_le_add_iff_left] using hs x hx
      _ = ρ := by simp [δ, ρ, add_comm]
  have hmeasure :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) =
          μ A := by
        rw [hA, measure_biUnion_finset hdisj fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsubset
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hρ]
  have hcancel :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hmeasure
  simpa [δ, ρ] using hcancel

/-- Real-valued form of the volumetric packing estimate.-/
theorem finset_card_le_volume_ratio
    (s : Finset E) {R eps : ℝ} (hR : 0 ≤ R) (heps : 0 < eps)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → eps ≤ ‖c - d‖) :
    (s.card : ℝ) ≤
      (R + eps / 2) ^ finrank ℝ E / (eps / 2) ^ finrank ℝ E := by
  classical
  by_cases hs0 : s = ∅
  · subst s
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hδpow : 0 < (eps / 2) ^ finrank ℝ E := by positivity
  have hρpow : 0 ≤ (R + eps / 2) ^ finrank ℝ E := by positivity
  have h := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2
    (finset_card_mul_ballVolume_le s heps hs hsep)
  rw [ENNReal.toReal_mul] at h
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hδpow.le,
    ENNReal.toReal_ofReal hρpow] at h
  exact (le_div_iff₀ hδpow).2 h

/-- A finite `ε`-separated family in the unit ball has at most
`(1 + 2 / ε)^dim` points.-/
theorem finset_card_le_one_add_two_div_pow
    (s : Finset E) {eps : ℝ} (heps : 0 < eps)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → eps ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (1 + 2 / eps) ^ finrank ℝ E := by
  have h := finset_card_le_volume_ratio s (by norm_num) heps hs hsep
  calc
    (s.card : ℝ) ≤
        (1 + eps / 2) ^ finrank ℝ E / (eps / 2) ^ finrank ℝ E := h
    _ = ((1 + eps / 2) / (eps / 2)) ^ finrank ℝ E :=
      (div_pow (1 + eps / 2) (eps / 2) (finrank ℝ E)).symm
    _ = (1 + 2 / eps) ^ finrank ℝ E := by
      congr 1
      field_simp
      ring

end VolumetricPacking

/-- Every compact set has finite packing number at positive radius.-/
theorem packingNumber_ne_top_of_isCompact
    {X : Type*} [PseudoMetricSpace X]
    (D : Set X) (hD : IsCompact D) {eps : ℝ≥0} (heps : 0 < eps) :
    Metric.packingNumber eps D ≠ ⊤ := by
  obtain ⟨T, hTD, hTfinite, hcoverOpen⟩ :=
    finite_cover_balls_of_compact hD
      (show 0 < (eps : ℝ) / 2 by positivity)
  classical
  let N : Finset X := hTfinite.toFinset
  have hcover : Metric.IsCover (eps / 2) D (N : Set X) := by
    intro x hx
    have hxcover := hcoverOpen hx
    simp only [Set.mem_iUnion, Metric.mem_ball] at hxcover
    obtain ⟨y, hyT, hxy⟩ := hxcover
    refine ⟨y, by simpa [N] using hyT, ?_⟩
    change edist x y ≤ (eps / 2 : ℝ≥0)
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    simpa using hxy.le
  have hext : Metric.externalCoveringNumber (eps / 2) D ≤ (N : Set X).encard :=
    hcover.externalCoveringNumber_le_encard
  have hpack : Metric.packingNumber eps D ≤ (N : Set X).encard := by
    have h :=
      (Metric.packingNumber_two_mul_le_externalCoveringNumber (eps / 2) D).trans hext
    have heq : 2 * (eps / 2) = eps := by field_simp
    rwa [heq] at h
  exact ne_top_of_le_ne_top (by simp) hpack

section UnitBallNet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Internal finite net of the unit ball with the standard volumetric
cardinality bound.-/
theorem exists_unitBall_finset_net_card_le
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) ∧
      (N.card : ℝ) ≤ (1 + 2 / eps) ^ finrank ℝ E := by
  classical
  let epsNN : ℝ≥0 := ⟨eps, heps.le⟩
  let D : Set E := closedBall (0 : E) 1
  have hD : IsCompact D := isCompact_closedBall (0 : E) 1
  have htop : Metric.packingNumber epsNN D ≠ ⊤ :=
    packingNumber_ne_top_of_isCompact D hD (by exact_mod_cast heps)
  let C : Set E := Metric.maximalSeparatedSet epsNN D
  have hCfinite : C.Finite := by
    rw [← Set.encard_ne_top_iff]
    simpa only [C, Metric.encard_maximalSeparatedSet htop] using htop
  let N : Finset E := hCfinite.toFinset
  have hNC : (N : Set E) = C := by simp [N]
  have hNmem : ∀ v ∈ N, ‖v‖ ≤ 1 := by
    intro v hv
    have hvN : v ∈ (N : Set E) := by simpa using hv
    have hvC : v ∈ C := hNC ▸ hvN
    have hvD : v ∈ D := Metric.maximalSeparatedSet_subset hvC
    simpa [D, mem_closedBall, dist_zero_right] using hvD
  have hNsep : ∀ c ∈ N, ∀ d ∈ N, c ≠ d → eps ≤ ‖c - d‖ := by
    intro c hc d hd hcd
    have hcN : c ∈ (N : Set E) := by simpa using hc
    have hdN : d ∈ (N : Set E) := by simpa using hd
    have hcC : c ∈ C := hNC ▸ hcN
    have hdC : d ∈ C := hNC ▸ hdN
    have h := Metric.isSeparated_maximalSeparatedSet hcC hdC hcd
    have hreal : eps < dist c d := by
      change (epsNN : ℝ≥0∞) < edist c d at h
      rw [edist_dist, ENNReal.coe_lt_ofReal] at h
      exact h
    rw [dist_eq_norm] at hreal
    exact hreal.le
  have hNcover : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps := by
    intro u hu
    have huD : u ∈ D := by
      simpa [D, mem_closedBall, dist_zero_right] using hu
    obtain ⟨v, hvC, huv⟩ := Metric.isCover_maximalSeparatedSet htop huD
    have hvN : v ∈ (N : Set E) := hNC.symm ▸ hvC
    refine ⟨v, by simpa using hvN, ?_⟩
    change edist u v ≤ (epsNN : ℝ≥0∞) at huv
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at huv
    change ENNReal.ofReal (dist u v) ≤ ENNReal.ofReal eps at huv
    exact (ENNReal.ofReal_le_ofReal_iff heps.le).mp huv
  refine ⟨N, hNmem, hNcover, ?_⟩
  exact finset_card_le_one_add_two_div_pow N heps hNmem hNsep

/-- For `ε ≤ 1`, the volumetric factor simplifies to `(3 / ε)^dim`.-/
theorem exists_unitBall_finset_net_card_le_three_div
    {eps : ℝ} (heps : 0 < eps) (heps_one : eps ≤ 1) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) ∧
      (N.card : ℝ) ≤ (3 / eps) ^ finrank ℝ E := by
  obtain ⟨N, hNmem, hNcover, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  refine ⟨N, hNmem, hNcover, hcard.trans ?_⟩
  apply pow_le_pow_left₀
  · positivity
  · apply (le_div_iff₀ heps).2
    calc
      (1 + 2 / eps) * eps = eps + 2 := by field_simp
      _ ≤ 3 := by linarith

end UnitBallNet

/-! ## Dimension-explicit iid concentration -/

/-- Iid random-set concentration with the volumetric entropy factor.-/
theorem hausdorffDist_convexified_iid_risk_bound_dimensional
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R)
    {n : ℕ} (hn : 0 < n) {eps t : ℝ}
    (heps : 0 < eps) (ht : 0 ≤ t) :
    μ.real {ω | t + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
          (iidAumannTarget μ (X 0) F)} ≤
      (1 + 2 / eps) ^ finrank ℝ E *
        symmetricSupportHoeffdingTail n t (R + R) := by
  obtain ⟨N, hN, hnet, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  have hprob := hausdorffDist_convexified_iid_risk_bound_of_hoeffding
    (μ := μ) X hX hindep hident F hF hFcompact hFne hFbound
    hn heps.le ht N hN hnet
  exact hprob.trans (mul_le_mul_of_nonneg_right hcard (by
    unfold symmetricSupportHoeffdingTail
    positivity))

/-- Closed-form dimension-explicit iid random-set concentration.-/
theorem hausdorffDist_convexified_iid_risk_bound_dimensional_standard
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hR : 0 < R)
    (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R)
    {n : ℕ} (hn : 0 < n) {eps t : ℝ}
    (heps : 0 < eps) (ht : 0 ≤ t) :
    μ.real {ω | t + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
          (iidAumannTarget μ (X 0) F)} ≤
      (1 + 2 / eps) ^ finrank ℝ E *
        (2 * exp (-(n : ℝ) * t ^ 2 / (2 * (R + R) ^ 2))) := by
  have hbound := hausdorffDist_convexified_iid_risk_bound_dimensional
    (μ := μ) X hX hindep hident F hF hFcompact hFne hFbound
    hn heps ht
  rw [symmetricSupportHoeffdingTail_eq hn t (by linarith : 0 < R + R)] at hbound
  exact hbound

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
