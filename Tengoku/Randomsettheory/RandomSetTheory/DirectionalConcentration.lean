/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.LimitTheorems
import Tengoku.Seed.Probability.Moments.SubGaussian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directional concentration for empirical Minkowski averages

This file turns scalar Hoeffding inequalities for support functions into
finite-sample concentration results for random compact convex sets.  The
sample is indexed by an arbitrary finite set, so the same API applies to
`Fin n`, `Finset.range n`, and finite subsamples of a general family.

The final result combines the directional estimates on a finite net with
`measure_hausdorffDist_gt_le_finset_support` from `LimitTheorems`.
-/

open Real Set Metric Finset MeasureTheory
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Hoeffding's inequality for a finite sum of independent, centered,
almost-everywhere bounded real random variables.-/
theorem hoeffding_finset_sum_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (a b : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤
      exp (-ε ^ 2 / (2 * (↑(∑ i ∈ s,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  apply HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (c := fun i => (‖b i - a i‖₊ / 2) ^ 2) h_indep _ hε
  intro i _hi
  exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (h_meas i) (h_bounds i) (h_centered i)

/-- Bilateral Hoeffding bound for a finite sum.  Unlike the average form
below, this statement does not require the index set to be nonempty and is
the convenient interface for truncation arguments.-/
theorem hoeffding_finset_sum_abs_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (a b : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    (s : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-t ^ 2 / (2 * (↑(∑ i ∈ s,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_neg : iIndepFun Xneg μ := by
    exact (h_indep.comp (fun _i => fun x : ℝ => -x) (fun _i => measurable_neg)).congr
      (fun _i => ae_of_all μ fun _ω => rfl)
  have h_meas_neg : ∀ i, AEMeasurable (Xneg i) μ := fun i => (h_meas i).neg
  have h_bounds_neg : ∀ i, ∀ᵐ ω ∂μ, Xneg i ω ∈ Icc (-b i) (-a i) := by
    intro i
    filter_upwards [h_bounds i] with ω hω
    exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩
  have h_centered_neg : ∀ i, μ[Xneg i] = 0 := by
    intro i
    simp only [Xneg]
    rw [integral_neg, h_centered i, neg_zero]
  have hpos := hoeffding_finset_sum_real X a b h_indep h_meas h_bounds
    h_centered s ht
  have hneg := hoeffding_finset_sum_real Xneg (-b) (-a) h_indep_neg h_meas_neg
    h_bounds_neg h_centered_neg s ht
  have hset : {ω | t ≤ |∑ i ∈ s, X i ω|} =
      {ω | t ≤ ∑ i ∈ s, X i ω} ∪
      {ω | t ≤ ∑ i ∈ s, Xneg i ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Xneg]
    rw [show (∑ i ∈ s, -X i ω) = -(∑ i ∈ s, X i ω) by simp]
    rw [le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | t ≤ ∑ i ∈ s, X i ω} +
        μ.real {ω | t ≤ ∑ i ∈ s, Xneg i ω} :=
      measureReal_union_le _ _
    _ ≤ exp (-t ^ 2 / (2 * (↑(∑ i ∈ s,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) +
        exp (-t ^ 2 / (2 * (↑(∑ i ∈ s,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      apply add_le_add hpos
      simpa [Xneg, sub_eq_add_neg, add_comm] using hneg
    _ = 2 * exp (-t ^ 2 / (2 * (↑(∑ i ∈ s,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      ring

/-- One-sided Hoeffding bound for the arithmetic average over a nonempty
finite index set.-/
theorem hoeffding_finset_average_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (a b : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    (s : Finset ι) (hs : s.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      exp (-((s.card : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ s,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  have h := hoeffding_finset_sum_real X a b h_indep h_meas h_bounds h_centered
    s (mul_nonneg (Nat.cast_nonneg s.card) ht)
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hs)
  have hset : {ω | t ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} =
      {ω | (s.card : ℝ) * t ≤ ∑ i ∈ s, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [le_div_iff₀ hcard]
    ring_nf
  rw [hset]
  exact h

/-- Bilateral Hoeffding bound for the arithmetic average over a nonempty
finite index set.-/
theorem hoeffding_finset_average_abs_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (a b : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    (s : Finset ι) (hs : s.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      2 * exp (-((s.card : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ s,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_neg : iIndepFun Xneg μ := by
    exact (h_indep.comp (fun _i => fun x : ℝ => -x) (fun _i => measurable_neg)).congr
      (fun _i => ae_of_all μ fun _ω => rfl)
  have h_meas_neg : ∀ i, AEMeasurable (Xneg i) μ := fun i => (h_meas i).neg
  have h_bounds_neg : ∀ i, ∀ᵐ ω ∂μ, Xneg i ω ∈ Icc (-b i) (-a i) := by
    intro i
    filter_upwards [h_bounds i] with ω hω
    exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩
  have h_centered_neg : ∀ i, μ[Xneg i] = 0 := by
    intro i
    simp only [Xneg]
    rw [integral_neg, h_centered i, neg_zero]
  have hpos := hoeffding_finset_average_real X a b h_indep h_meas h_bounds
    h_centered s hs ht
  have hneg := hoeffding_finset_average_real Xneg (-b) (-a) h_indep_neg h_meas_neg
    h_bounds_neg h_centered_neg s hs ht
  have hset : {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} =
      {ω | t ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ∪
      {ω | t ≤ (∑ i ∈ s, Xneg i ω) / (s.card : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Xneg]
    rw [show (∑ i ∈ s, -X i ω) = -(∑ i ∈ s, X i ω) by simp]
    rw [neg_div, le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | t ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} +
        μ.real {ω | t ≤ (∑ i ∈ s, Xneg i ω) / (s.card : ℝ)} :=
      measureReal_union_le _ _
    _ ≤ exp (-((s.card : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ s,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) +
        exp (-((s.card : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ s,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      apply add_le_add hpos
      simpa [Xneg, sub_eq_add_neg, add_comm] using hneg
    _ = 2 * exp (-((s.card : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ s,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      ring

end ProbabilityTheory

namespace RandomSetTheory

variable {Ω ι E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Centered support-function contribution in direction `u`.-/
def directionalSupportDeviation
    (S : ι → Ω → Set E) (L : Set E) (u : E) (i : ι) (ω : Ω) : ℝ :=
  supportFunction (S i ω) u - supportFunction L u

/-- A compact set contained in a radius-`R` ball has support function bounded
by `R` in absolute value along every direction of norm at most one.-/
theorem abs_supportFunction_le_radius {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) {u : E} (hu : ‖u‖ ≤ 1) :
    |supportFunction K u| ≤ R := by
  obtain ⟨x, hx, hmax⟩ := supportFunction_attains hK hKne u
  rw [hmax]
  calc
    |⟪u, x⟫_ℝ| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * R := mul_le_mul hu (hR x hx) (norm_nonneg x) (by norm_num)
    _ = R := one_mul R

omit [MeasurableSpace Ω] in
/-- Radius bounds give the symmetric interval needed by Hoeffding for a
directional support deviation.-/
theorem directionalSupportDeviation_mem_Icc_of_radius
    (S : ι → Ω → Set E) (L : Set E) (u : E) (i : ι) (ω : Ω)
    {RS RL : ℝ}
    (hScompact : IsCompact (S i ω)) (hSne : (S i ω).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hRS : ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL) (hu : ‖u‖ ≤ 1) :
    directionalSupportDeviation S L u i ω ∈ Icc (-(RS + RL)) (RS + RL) := by
  have hS := abs_supportFunction_le_radius hScompact hSne hRS hu
  have hL := abs_supportFunction_le_radius hLcompact hLne hRL hu
  unfold directionalSupportDeviation
  constructor <;>
    linarith [le_abs_self (supportFunction (S i ω) u),
      neg_le_abs (supportFunction (S i ω) u),
      le_abs_self (supportFunction L u), neg_le_abs (supportFunction L u)]

/-- A common radius bound is preserved by a nonempty Minkowski average.-/
theorem norm_le_radius_of_mem_nonempty_minkowskiAverage
    (s : Finset ι) (hs : s.Nonempty) (K : ι → Set E) {R : ℝ}
    (hR : ∀ i ∈ s, ∀ x ∈ K i, ‖x‖ ≤ R)
    {x : E} (hx : x ∈ minkowskiAverage s K) :
    ‖x‖ ≤ R := by
  have h := norm_le_average_radius_of_mem_minkowskiAverage
    s K (fun _ => R) hR hx
  calc
    ‖x‖ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, R := h
    _ = R := by
      simp only [sum_const, nsmul_eq_mul]
      field_simp [Finset.card_ne_zero.mpr hs]

omit [MeasurableSpace Ω] in
/-- The support-function error of a Minkowski average is the average of the
directional support deviations.-/
theorem supportFunction_minkowskiAverage_sub_eq_average_deviation
    (S : ι → Ω → Set E) (L : Set E) (s : Finset ι) (hs : s.Nonempty)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    (ω : Ω) (u : E) :
    supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u =
      (∑ i ∈ s, directionalSupportDeviation S L u i ω) / (s.card : ℝ) := by
  rw [supportFunction_minkowskiAverage s (fun i => S i ω)
    (fun i hi => hScompact i hi ω) (fun i hi => hSne i hi ω)]
  simp only [directionalSupportDeviation, sum_sub_distrib, sum_const,
    nsmul_eq_mul, div_eq_inv_mul]
  field_simp [Finset.card_ne_zero.mpr hs]

/-- Directional Hoeffding inequality for a finite empirical Minkowski
average.-/
theorem minkowskiAverage_support_hoeffding
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (a b : ι → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (h_meas : ∀ i, AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ,
      directionalSupportDeviation S L u i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[directionalSupportDeviation S L u i] = 0)
    (s : Finset ι) (hs : s.Nonempty)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      2 * exp (-((s.card : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ s,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  have htail := ProbabilityTheory.hoeffding_finset_average_abs_real
    (directionalSupportDeviation S L u) a b h_indep h_meas h_bounds
    h_centered s hs ht
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

/-- The explicit bilateral Hoeffding tail for a sample of size `m` and a
symmetric bound `[-B,B]`.-/
def symmetricSupportHoeffdingTail (m : ℕ) (t B : ℝ) : ℝ :=
  2 * exp (-((m : ℝ) * t) ^ 2 / (2 * ((m : ℝ) * B ^ 2)))

/-- Standard simplification of the symmetric Hoeffding proxy.-/
theorem symmetricSupportHoeffdingTail_eq
    {m : ℕ} (hm : 0 < m) (t : ℝ) {B : ℝ} (hB : 0 < B) :
    symmetricSupportHoeffdingTail m t B =
      2 * exp (-(m : ℝ) * t ^ 2 / (2 * B ^ 2)) := by
  unfold symmetricSupportHoeffdingTail
  congr 2
  field_simp [Nat.cast_ne_zero.mpr hm.ne', hB.ne']

/-- Radius-specialized directional Hoeffding bound.  Apart from independence,
measurability, and centering, all scalar boundedness assumptions have been
discharged geometrically.-/
theorem minkowskiAverage_support_hoeffding_of_radius
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    {RS RL : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hu : ‖u‖ ≤ 1)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (h_meas : ∀ i, AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_centered : ∀ i, μ[directionalSupportDeviation S L u i] = 0)
    (s : Finset ι) (hs : s.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      symmetricSupportHoeffdingTail s.card t (RS + RL) := by
  have htail := minkowskiAverage_support_hoeffding S L u
    (fun _ => -(RS + RL)) (fun _ => RS + RL)
    h_indep h_meas
    (fun i => ae_of_all μ fun ω =>
      directionalSupportDeviation_mem_Icc_of_radius S L u i ω
        (hScompact i ω) (hSne i ω) hLcompact hLne
        (hRS i ω) hRL hu)
    h_centered s hs
    (fun i _hi ω => hScompact i ω)
    (fun i _hi ω => hSne i ω) ht
  have hsum :
      (↑(∑ i ∈ s,
        (((‖(RS + RL) - (-(RS + RL))‖₊ / (2 : NNReal)) ^ (2 : ℕ)) :
          NNReal) : NNReal) : ℝ) =
        (s.card : ℝ) * (RS + RL) ^ 2 := by
    push_cast
    rw [sum_const, nsmul_eq_mul]
    congr 1
    simp only [Real.norm_eq_abs, sub_neg_eq_add]
    rw [← two_mul, abs_mul]
    norm_num
  simpa only [symmetricSupportHoeffdingTail, hsum] using htail

/-- Real-valued finite-net version of the Hausdorff transfer theorem from
`LimitTheorems`.-/
theorem measureReal_hausdorffDist_gt_le_finset_support
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (K L : Ω → Set E)
    (hKcompact : ∀ ω, IsCompact (K ω))
    (hLcompact : ∀ ω, IsCompact (L ω))
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : ∀ ω, (L ω).Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω)) (hLconv : ∀ ω, Convex ℝ (L ω))
    {RK RL eps t q : ℝ}
    (hRK : ∀ ω, ∀ x ∈ K ω, ‖x‖ ≤ RK)
    (hRL : ∀ ω, ∀ x ∈ L ω, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (htail : ∀ v ∈ N, μ.real {ω |
      t < |supportFunction (K ω) v - supportFunction (L ω) v|} ≤ q) :
    μ.real {ω | t + (RK + RL) * eps < hausdorffDist (K ω) (L ω)} ≤
      N.card * q := by
  have htailENN : ∀ v ∈ N, μ {ω |
      t < |supportFunction (K ω) v - supportFunction (L ω) v|} ≤
        ENNReal.ofReal q := by
    intro v hv
    rw [← MeasureTheory.ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (htail v hv)
  have hbound := measure_hausdorffDist_gt_le_finset_support
    hKcompact hLcompact hKne hLne hKconv hLconv hRK hRL
    heps ht N hnet htailENN
  have hleft : μ {ω |
      t + (RK + RL) * eps < hausdorffDist (K ω) (L ω)} ≠ ∞ := by
    finiteness
  have hright : (∑ _v ∈ N, ENNReal.ofReal q) ≠ ∞ := by
    rw [sum_const, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have hreal := (ENNReal.toReal_le_toReal hleft hright).2 hbound
  simpa [Measure.real, ENNReal.toReal_ofReal hq] using hreal

/-- Complete finite-net Hausdorff concentration theorem for an empirical
Minkowski average.-/
theorem hausdorffDist_minkowskiAverage_risk_bound_of_hoeffding
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (N : Finset E) (hN : ∀ v ∈ N, ‖v‖ ≤ 1)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (h_indep : ∀ v ∈ N, ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L v) μ)
    (h_meas : ∀ v ∈ N, ∀ i,
      AEMeasurable (directionalSupportDeviation S L v i) μ)
    (h_centered : ∀ v ∈ N, ∀ i,
      μ[directionalSupportDeviation S L v i] = 0) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * symmetricSupportHoeffdingTail s.card t (RS + RL) := by
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
    (by unfold symmetricSupportHoeffdingTail; positivity)
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
    _ ≤ symmetricSupportHoeffdingTail s.card t (RS + RL) :=
      minkowskiAverage_support_hoeffding_of_radius
        S L v hScompact hSne hLcompact hLne hRS hRL (hN v hv)
        (h_indep v hv) (h_meas v hv) (h_centered v hv) s hs ht

/-- Closed-form version of the finite-net Hausdorff bound.-/
theorem hausdorffDist_minkowskiAverage_risk_bound_standard
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hB : 0 < RS + RL)
    (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (N : Finset E) (hN : ∀ v ∈ N, ‖v‖ ≤ 1)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (h_indep : ∀ v ∈ N, ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L v) μ)
    (h_meas : ∀ v ∈ N, ∀ i,
      AEMeasurable (directionalSupportDeviation S L v i) μ)
    (h_centered : ∀ v ∈ N, ∀ i,
      μ[directionalSupportDeviation S L v i] = 0) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * (2 * exp (-(s.card : ℝ) * t ^ 2 /
        (2 * (RS + RL) ^ 2))) := by
  have hbound := hausdorffDist_minkowskiAverage_risk_bound_of_hoeffding
    (μ := μ) S L s hs hScompact hSne hSconv hLcompact hLne hLconv
    hRS hRL heps ht N hN hnet h_indep h_meas h_centered
  rw [symmetricSupportHoeffdingTail_eq (Finset.card_pos.mpr hs) t hB] at hbound
  exact hbound

end RandomSetTheory
