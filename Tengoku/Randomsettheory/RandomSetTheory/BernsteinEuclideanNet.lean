/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.BernsteinConcentration
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanNetCardinality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dimension-explicit Bernstein concentration

This module combines the Bernstein support-process bound with the standard
volumetric net of the Euclidean unit ball.  It removes the abstract finite
net from the final inequality and exposes the entropy factor
`(1 + 2 / ε)^dim` used in finite-dimensional random-set concentration.
-/

open Real Set Metric Finset MeasureTheory Module
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal ENNReal

noncomputable section

namespace RandomSetTheory

/-- Dimension-explicit Hausdorff Bernstein inequality.  Directional
independence and Bernstein MGF bounds are required uniformly on the unit
ball; the volumetric construction chooses the finite directions
automatically.
@isnad1 id=le.14h13v.s9.e59ff2582197 from=translated src=- shape=ba3b8268 vocab=089f04b6
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_dimensional_of_bernstein
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (ht : 0 ≤ t)
    (h_indep : ∀ w : E, ‖w‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hB : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ s,
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation S L w i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      (1 + 2 / eps) ^ finrank ℝ E *
        (2 * exp (-((s.card : ℝ) * t) ^ 2 /
          (2 * (((∑ i ∈ s, v i : ℝ≥0) : ℝ) +
            (b : ℝ) * ((s.card : ℝ) * t))))) := by
  obtain ⟨N, hN, hnet, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  have hprob := hausdorffDist_minkowskiAverage_risk_bound_of_bernstein
    S L s hs v b hScompact hSne hSconv hLcompact hLne hLconv
    hRS hRL heps.le ht N hnet
    (fun w hw => h_indep w (hN w hw))
    (fun w hw => hB w (hN w hw)) hV
  exact hprob.trans (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- Dimension-explicit confidence-parameter form.  The Hausdorff deviation
threshold is the finite-net interpolation error plus
`(sqrt (2 V x) + 2 b x) / n`.
@isnad1 id=le.14h13v.s9.0a0e70c6c0ca from=translated src=- shape=264c2e43 vocab=314f7813
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_dimensional_bernstein_sqrt_add
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    {RS RL eps x : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ y ∈ S i ω, ‖y‖ ≤ RS)
    (hRL : ∀ y ∈ L, ‖y‖ ≤ RL)
    (heps : 0 < eps) (hx : 0 ≤ x)
    (h_indep : ∀ w : E, ‖w‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hB : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ s,
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation S L w i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) + (RS + RL) * eps <
          hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      (1 + 2 / eps) ^ finrank ℝ E * (2 * exp (-x)) := by
  obtain ⟨N, hN, hnet, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  have hprob :=
    hausdorffDist_minkowskiAverage_risk_bound_bernstein_sqrt_add
      S L s hs v b hScompact hSne hSconv hLcompact hLne hLconv
      hRS hRL heps.le hx N hnet
      (fun w hw => h_indep w (hN w hw))
      (fun w hw => hB w (hN w hw)) hV
  exact hprob.trans (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- Confidence-level form of the dimension-explicit Bernstein inequality.
The logarithmic confidence parameter absorbs both the bilateral factor and
the volumetric entropy factor, so the right-hand side is exactly `δ`.
@isnad1 id=le.15h13v.s9.7ffbf6b97134 from=translated src=- shape=1d14ec7b vocab=40a3b0ee
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_dimensional_bernstein_confidence
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    {RS RL eps δ : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ y ∈ S i ω, ‖y‖ ≤ RS)
    (hRL : ∀ y ∈ L, ‖y‖ ≤ RL)
    (heps : 0 < eps) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (h_indep : ∀ w : E, ‖w‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hB : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ s,
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation S L w i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) *
              Real.log
                (2 * (1 + 2 / eps) ^ finrank ℝ E / δ)) +
            2 * (b : ℝ) *
              Real.log
                (2 * (1 + 2 / eps) ^ finrank ℝ E / δ)) /
            (s.card : ℝ) + (RS + RL) * eps <
          hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤ δ := by
  let C : ℝ := (1 + 2 / eps) ^ finrank ℝ E
  let x : ℝ := Real.log (2 * C / δ)
  have hbase : 1 ≤ 1 + 2 / eps := by
    have : 0 ≤ 2 / eps := by positivity
    linarith
  have hC : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ hbase
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have harg : 1 ≤ 2 * C / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hargpos : 0 < 2 * C / δ := lt_of_lt_of_le zero_lt_one harg
  have hx : 0 ≤ x := by
    dsimp [x]
    exact Real.log_nonneg harg
  have hprob :=
    hausdorffDist_minkowskiAverage_risk_bound_dimensional_bernstein_sqrt_add
      S L s hs v b hScompact hSne hSconv hLcompact hLne hLconv
      hRS hRL heps hx h_indep hB hV
  change μ.real {ω |
      (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
          2 * (b : ℝ) * x) / (s.card : ℝ) + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤ δ
  refine hprob.trans ?_
  change C * (2 * exp (-x)) ≤ δ
  have heq : C * (2 * exp (-x)) = δ := by
    rw [Real.exp_neg]
    have hexp : Real.exp x = 2 * C / δ := by
      dsimp [x]
      exact Real.exp_log hargpos
    rw [hexp]
    field_simp [hδ.ne', hCpos.ne']
  exact heq.le

end RandomSetTheory
