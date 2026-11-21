/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.DirectionalConcentration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sub-Gaussian concentration for empirical Minkowski averages

This file complements the bounded-variable Hoeffding results in
`DirectionalConcentration` with hypotheses stated directly in terms of
`ProbabilityTheory.HasSubgaussianMGF`.

For independent variables with respective variance proxies `c i`, the proxy
of their sum is exactly `∑ i ∈ s, c i`.  We first derive bilateral bounds for
finite sums and averages, then apply them to directional support deviations.
A final finite-net argument turns the directional estimates into a Hausdorff
concentration bound for empirical Minkowski averages.
-/

open Real Set Metric Finset MeasureTheory
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bilateral sub-Gaussian tail for a finite sum of independent real random
variables.  The variance proxy is the sum of the individual proxies.
@isnad1 id=le.3h7v.s7.8991c0174dfa from=translated src=- shape=2d63d923 vocab=bad116fd
-/
theorem subgaussian_finset_sum_abs_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (c : ι → ℝ≥0)
    (h_indep : iIndepFun X μ)
    (s : Finset ι)
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-ε ^ 2 / (2 * (↑(∑ i ∈ s, c i) : ℝ))) := by
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_neg : iIndepFun Xneg μ := by
    exact (h_indep.comp (fun _i => fun x : ℝ => -x) (fun _i => measurable_neg)).congr
      (fun _i => ae_of_all μ fun _ω => rfl)
  have h_subG_neg : ∀ i ∈ s, HasSubgaussianMGF (Xneg i) (c i) μ := by
    intro i hi
    exact (h_subG i hi).neg
  have hpos := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    h_indep h_subG hε
  have hneg := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    h_indep_neg h_subG_neg hε
  have hset : {ω | ε ≤ |∑ i ∈ s, X i ω|} =
      {ω | ε ≤ ∑ i ∈ s, X i ω} ∪
      {ω | ε ≤ ∑ i ∈ s, Xneg i ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Xneg]
    rw [show (∑ i ∈ s, -X i ω) = -(∑ i ∈ s, X i ω) by simp]
    rw [le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} +
        μ.real {ω | ε ≤ ∑ i ∈ s, Xneg i ω} :=
      measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * (↑(∑ i ∈ s, c i) : ℝ))) +
        exp (-ε ^ 2 / (2 * (↑(∑ i ∈ s, c i) : ℝ))) :=
      add_le_add hpos hneg
    _ = 2 * exp (-ε ^ 2 / (2 * (↑(∑ i ∈ s, c i) : ℝ))) := by ring

/-- Bilateral sub-Gaussian tail for the arithmetic average over a nonempty
finite set.  No common-proxy assumption is imposed.
@isnad1 id=le.4h7v.s7.1ae01a224fae from=translated src=- shape=c9ebff35 vocab=7e71b42b
-/
theorem subgaussian_finset_average_abs_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (c : ι → ℝ≥0)
    (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty)
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (↑(∑ i ∈ s, c i) : ℝ))) := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hs)
  have htail := subgaussian_finset_sum_abs_real X c h_indep s h_subG
    (mul_nonneg (Nat.cast_nonneg s.card) ht)
  have hset : {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} =
      {ω | (s.card : ℝ) * t ≤ |∑ i ∈ s, X i ω|} := by
    ext ω
    simp only [mem_ofPred_eq, abs_div, abs_of_pos hcard]
    rw [le_div_iff₀ hcard]
    ring_nf
  rw [hset]
  exact htail

end ProbabilityTheory

namespace RandomSetTheory

variable {Ω ι E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Directional sub-Gaussian concentration for an empirical Minkowski
average.  The centeredness of the directional deviations is encoded in the
`HasSubgaussianMGF` hypotheses.
@isnad1 id=le.6h10v.s8.90b1ead17a8a from=translated src=- shape=4538fe32 vocab=2124d8c9
-/
theorem minkowskiAverage_support_subgaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (c : ι → ℝ≥0)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (s : Finset ι) (hs : s.Nonempty)
    (h_subG : ∀ i ∈ s, ProbabilityTheory.HasSubgaussianMGF
      (directionalSupportDeviation S L u i) (c i) μ)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (↑(∑ i ∈ s, c i) : ℝ))) := by
  have htail := ProbabilityTheory.subgaussian_finset_average_abs_real
    (directionalSupportDeviation S L u) c h_indep s hs h_subG ht
  have hset :
      {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} =
      {ω | t ≤ |(∑ i ∈ s, directionalSupportDeviation S L u i ω) /
        (s.card : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L s hs hScompact hSne]
  rw [hset]
  exact htail

/-- Finite-net Hausdorff concentration for an empirical Minkowski average
whose directional support deviations are independent and sub-Gaussian with
direction-independent proxies `c i`.

The radius assumptions are only used to control the interpolation error
between directions of the finite net.
@isnad1 id=le.14h13v.s9.4cbc1a79cd06 from=translated src=- shape=0373d024 vocab=af6fddba
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_of_subgaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℝ≥0)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (h_indep : ∀ v ∈ N, ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L v) μ)
    (h_subG : ∀ v ∈ N, ∀ i ∈ s, ProbabilityTheory.HasSubgaussianMGF
      (directionalSupportDeviation S L v i) (c i) μ) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * (2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (↑(∑ i ∈ s, c i) : ℝ)))) := by
  apply measureReal_hausdorffDist_gt_le_finset_support
    (μ := μ) (fun ω => minkowskiAverage s (fun i => S i ω)) (fun _ => L)
    (fun ω => isCompact_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hScompact i ω))
    (fun _ => hLcompact)
    (fun ω => nonempty_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSne i ω))
    (fun _ => hLne)
    (fun ω => convex_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSconv i ω))
    (fun _ => hLconv)
    (fun ω x hx => norm_le_radius_of_mem_nonempty_minkowskiAverage s hs
      (fun i => S i ω) (fun i hi => hRS i ω) hx)
    (fun _ => hRL) heps ht
    (by positivity)
    N hnet
  intro v hv
  calc
    μ.real {ω | t < |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
        supportFunction L v|} ≤
        μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
          supportFunction L v|} := by
      apply measureReal_mono
      · intro ω hω
        change t < |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
          supportFunction L v| at hω
        change t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
          supportFunction L v|
        exact hω.le
      · finiteness
    _ ≤ 2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (↑(∑ i ∈ s, c i) : ℝ))) :=
      minkowskiAverage_support_subgaussian S L v c
        (h_indep v hv) s hs (h_subG v hv)
        (fun i _hi ω => hScompact i ω)
        (fun i _hi ω => hSne i ω) ht

end RandomSetTheory
