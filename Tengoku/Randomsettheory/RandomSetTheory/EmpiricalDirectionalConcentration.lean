/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteNetSetConcentration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directional concentration for empirical Minkowski averages

This file specializes the scalar Hoeffding machinery to support functions of
independent random compact sets.
-/

open Real Set Metric Finset MeasureTheory
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- One-sided Hoeffding bound for an average indexed exactly by `Fin n`.
Unlike `hoeffding_average_real`, it has no assumptions outside the sample.-/
lemma hoeffding_fin_average_real [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (a b : Fin n → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ i, X i ω) / (n : ℝ)} ≤
      exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  have h := hoeffding_sum_real X a b h_indep h_meas h_bounds h_centered
    Finset.univ (mul_nonneg (Nat.cast_nonneg n) ht)
  have hset : {ω | t ≤ (∑ i, X i ω) / (n : ℝ)} =
      {ω | (n : ℝ) * t ≤ ∑ i, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [le_div_iff₀ (Nat.cast_pos.mpr hn)]
    ring
  rw [hset]
  exact h

/-- Bilateral Hoeffding bound for an average indexed exactly by `Fin n`.
Independence, measurability, bounds and centering are required only for the
finite sample family.-/
lemma hoeffding_fin_average_abs_real [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (a b : Fin n → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i, X i ω) / (n : ℝ)|} ≤
      2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  let Xneg : Fin n → Ω → ℝ := fun i ω => -X i ω
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
  have hpos := hoeffding_fin_average_real X a b h_indep h_meas h_bounds
    h_centered hn ht
  have hneg := hoeffding_fin_average_real Xneg (-b) (-a) h_indep_neg h_meas_neg
    h_bounds_neg h_centered_neg hn ht
  have hset : {ω | t ≤ |(∑ i, X i ω) / (n : ℝ)|} =
      {ω | t ≤ (∑ i, X i ω) / (n : ℝ)} ∪
      {ω | t ≤ (∑ i, Xneg i ω) / (n : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Xneg]
    rw [show (∑ i, -X i ω) = -(∑ i, X i ω) by simp]
    rw [neg_div, le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | t ≤ (∑ i, X i ω) / (n : ℝ)} +
        μ.real {ω | t ≤ (∑ i, Xneg i ω) / (n : ℝ)} :=
      measureReal_union_le _ _
    _ ≤ exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) +
        exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      apply add_le_add hpos
      simpa [Xneg, sub_eq_add_neg, add_comm] using hneg
    _ = 2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      ring

end ProbabilityTheory

namespace RandomSetTheory.Empirical

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The empirical Minkowski average of a sequence of random sets.-/
def empiricalMinkowskiAverage (S : ℕ → Ω → Set E) (n : ℕ) (ω : Ω) : Set E :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, S i ω

theorem empiricalMinkowskiAverage_compact
    (S : ℕ → Ω → Set E) (n : ℕ)
    (hS : ∀ i < n, ∀ ω, IsCompact (S i ω)) (ω : Ω) :
    IsCompact (empiricalMinkowskiAverage S n ω) := by
  unfold empiricalMinkowskiAverage
  apply (isCompact_finset_sum (range n) (fun i => S i ω) ?_).smul
  intro i hi
  exact hS i (mem_range.mp hi) ω

theorem empiricalMinkowskiAverage_nonempty
    (S : ℕ → Ω → Set E) (n : ℕ)
    (hS : ∀ i < n, ∀ ω, (S i ω).Nonempty) (ω : Ω) :
    (empiricalMinkowskiAverage S n ω).Nonempty := by
  unfold empiricalMinkowskiAverage
  exact (nonempty_finset_sum (range n) (fun i => S i ω)
    (fun i hi => hS i (mem_range.mp hi) ω)).smul_set

theorem empiricalMinkowskiAverage_convex
    (S : ℕ → Ω → Set E) (n : ℕ)
    (hS : ∀ i < n, ∀ ω, Convex ℝ (S i ω)) (ω : Ω) :
    Convex ℝ (empiricalMinkowskiAverage S n ω) := by
  unfold empiricalMinkowskiAverage
  apply Convex.smul
  exact convex_sum (fun i => S i ω)
    (fun i hi => hS i (mem_range.mp hi) ω)

/-- Averaging sets contained in the radius-`R` ball preserves the same
radius, rather than accumulating an `nR` bound.-/
theorem empiricalMinkowskiAverage_radius
    (S : ℕ → Ω → Set E) {n : ℕ} (hn : 0 < n) {R : ℝ}
    (hS : ∀ i < n, ∀ ω, ∀ x ∈ S i ω, ‖x‖ ≤ R) (ω : Ω) :
    ∀ x ∈ empiricalMinkowskiAverage S n ω, ‖x‖ ≤ R := by
  intro x hx
  unfold empiricalMinkowskiAverage at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Set.mem_finsetSum] at hy
  obtain ⟨g, hg, hsum⟩ := hy
  rw [← hsum, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ * ‖∑ i ∈ range n, g i‖ ≤
        (n : ℝ)⁻¹ * ∑ i ∈ range n, ‖g i‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ range n, R := by
      gcongr with i hi
      exact hS i (mem_range.mp hi) ω (g i) (hg hi)
    _ = R := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- Support functions commute with a nonnegative scalar dilation of a compact
nonempty set.-/
theorem supportFunction_smul_set {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    supportFunction (c • K) u = c * supportFunction K u := by
  have hCK : IsCompact (c • K) := hK.smul c
  have hCKne : (c • K).Nonempty := hKne.smul_set
  obtain ⟨y, hy, hymax⟩ := supportFunction_attains hCK hCKne u
  obtain ⟨x, hx, hxmax⟩ := supportFunction_attains hK hKne u
  apply le_antisymm
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [hymax, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_supportFunction hK hz u) hc
  · rw [hxmax, ← real_inner_smul_right]
    exact inner_le_supportFunction hCK (smul_mem_smul_set hx) u

/-- The support function of an empirical Minkowski average is the ordinary
empirical average of the individual support functions.-/
theorem supportFunction_empiricalMinkowskiAverage
    (S : ℕ → Ω → Set E) {n : ℕ}
    (hScompact : ∀ i < n, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i < n, ∀ ω, (S i ω).Nonempty)
    (ω : Ω) (u : E) :
    supportFunction (empiricalMinkowskiAverage S n ω) u =
      (∑ i ∈ range n, supportFunction (S i ω) u) / (n : ℝ) := by
  unfold empiricalMinkowskiAverage
  rw [supportFunction_smul_set
      (isCompact_finset_sum (range n) (fun i => S i ω)
        (fun i hi => hScompact i (mem_range.mp hi) ω))
      (nonempty_finset_sum (range n) (fun i => S i ω)
        (fun i hi => hSne i (mem_range.mp hi) ω))]
  · rw [supportFunction_finset_sum]
    · rw [div_eq_inv_mul]
    · intro i hi
      exact hScompact i (mem_range.mp hi) ω
    · intro i hi
      exact hSne i (mem_range.mp hi) ω
  · exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Centered support-function contribution in direction `u`.-/
def directionalSupportDeviation
    (S : ℕ → Ω → Set E) (L : Set E) (u : E) (i : ℕ) (ω : Ω) : ℝ :=
  supportFunction (S i ω) u - supportFunction L u

/-- A compact set contained in a ball of radius `R` has support function at
most `R` in absolute value along every unit direction.-/
theorem abs_supportFunction_le_radius {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) {u : E} (hu : ‖u‖ ≤ 1) :
    |supportFunction K u| ≤ R := by
  obtain ⟨x, hx, hmax⟩ := supportFunction_attains hK hKne u
  rw [hmax]
  calc
    |⟪u, x⟫_ℝ| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * R := by
      exact mul_le_mul hu (hR x hx) (norm_nonneg x) (by norm_num)
    _ = R := one_mul R

/-- Radius bounds automatically give the symmetric interval needed by
Hoeffding for a centered directional support contribution.-/
theorem directionalSupportDeviation_mem_Icc_of_radius
    (S : ℕ → Ω → Set E) (L : Set E) (u : E) (i : ℕ) (ω : Ω)
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

theorem supportFunction_empirical_sub_eq_average_deviation
    (S : ℕ → Ω → Set E) (L : Set E) {n : ℕ} (hn : 0 < n)
    (hScompact : ∀ i < n, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i < n, ∀ ω, (S i ω).Nonempty)
    (ω : Ω) (u : E) :
    supportFunction (empiricalMinkowskiAverage S n ω) u - supportFunction L u =
      (∑ i ∈ range n, directionalSupportDeviation S L u i ω) / (n : ℝ) := by
  rw [supportFunction_empiricalMinkowskiAverage S hScompact hSne]
  simp only [directionalSupportDeviation, sum_sub_distrib, sum_const, card_range,
    nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- Directional Hoeffding inequality for an empirical Minkowski average of
independent random compact sets. This is directly usable as the `htail`
hypothesis of the set-valued concentration theorems.-/
theorem empiricalMinkowskiAverage_support_hoeffding
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ℕ → Ω → Set E) (L : Set E) (u : E)
    (a b : ℕ → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (h_meas : ∀ i, AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ,
      directionalSupportDeviation S L u i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[directionalSupportDeviation S L u i] = 0)
    {n : ℕ} (hn : 0 < n)
    (hScompact : ∀ i < n, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i < n, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (empiricalMinkowskiAverage S n ω) u -
        supportFunction L u|} ≤
      2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  have htail := ProbabilityTheory.hoeffding_average_abs_real
    (directionalSupportDeviation S L u) a b h_indep h_meas h_bounds
    h_centered hn ht
  have hset : {ω | t ≤ |supportFunction (empiricalMinkowskiAverage S n ω) u -
        supportFunction L u|} =
      {ω | t ≤ |(∑ i ∈ range n, directionalSupportDeviation S L u i ω) /
        (n : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_empirical_sub_eq_average_deviation
      S L hn hScompact hSne]
  rw [hset]
  exact htail

/-- The explicit Hoeffding tail corresponding to a symmetric bound `[-B,B]`.-/
def symmetricSupportHoeffdingTail (n : ℕ) (t B : ℝ) : ℝ :=
  2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ _i ∈ range n,
    (((‖B - (-B)‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ)))

/-- For a nonempty sample and a positive symmetric bound, the proxy sum in
`symmetricSupportHoeffdingTail` reduces to `n B²`, giving the standard
Hoeffding exponent.-/
theorem symmetricSupportHoeffdingTail_eq_standard
    {n : ℕ} (hn : 0 < n) (t : ℝ) {B : ℝ} (hB : 0 < B) :
    symmetricSupportHoeffdingTail n t B =
      2 * exp (-(n : ℝ) * t ^ 2 / (2 * B ^ 2)) := by
  have hwidth : ‖B - (-B)‖₊ / (2 : NNReal) = ⟨B, hB.le⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
      sub_neg_eq_add]
    rw [abs_of_pos (by linarith : 0 < B + B)]
    norm_num
    rfl
  have hsum :
      (↑(∑ _i ∈ range n,
        (((‖B - (-B)‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ) =
        (n : ℝ) * B ^ 2 := by
    rw [hwidth]
    push_cast
    rw [sum_const, card_range, nsmul_eq_mul]
    change (n : ℝ) * B ^ 2 = (n : ℝ) * B ^ 2
    rfl
  unfold symmetricSupportHoeffdingTail
  rw [hsum]
  congr 2
  field_simp [Nat.cast_ne_zero.mpr hn.ne', hB.ne']

/-- Fully geometric specialization: radius bounds discharge the boundedness
hypothesis of Hoeffding in every unit direction.-/
theorem empiricalMinkowskiAverage_support_hoeffding_of_radius
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ℕ → Ω → Set E) (L : Set E) (u : E)
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
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (empiricalMinkowskiAverage S n ω) u -
        supportFunction L u|} ≤
      symmetricSupportHoeffdingTail n t (RS + RL) := by
  unfold symmetricSupportHoeffdingTail
  apply empiricalMinkowskiAverage_support_hoeffding S L u
    (fun _ => -(RS + RL)) (fun _ => RS + RL)
    h_indep h_meas
  · intro i
    exact ae_of_all μ fun ω =>
      directionalSupportDeviation_mem_Icc_of_radius S L u i ω
        (hScompact i ω) (hSne i ω) hLcompact hLne
        (hRS i ω) hRL hu
  · exact h_centered
  · exact hn
  · exact fun i _hi ω => hScompact i ω
  · exact fun i _hi ω => hSne i ω
  · exact ht

/-- Complete finite-net Hausdorff concentration theorem for empirical
Minkowski averages. The only probabilistic assumptions left are independence,
measurability and centering of the concrete scalar support contributions.-/
theorem hausdorffDist_empiricalMinkowskiAverage_risk_bound_of_hoeffding
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ℕ → Ω → Set E) (L : Set E)
    {n : ℕ} (hn : 0 < n) {RS RL eps t : ℝ}
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
        hausdorffDist (empiricalMinkowskiAverage S n ω) L} ≤
      N.card * symmetricSupportHoeffdingTail n t (RS + RL) := by
  apply hausdorffDist_risk_bound_of_finset_supportFunction
    (μ := μ) (fun ω => empiricalMinkowskiAverage S n ω) L
    (fun ω => empiricalMinkowskiAverage_compact S n
      (fun i _hi ω => hScompact i ω) ω)
    hLcompact
    (fun ω => empiricalMinkowskiAverage_nonempty S n
      (fun i _hi ω => hSne i ω) ω)
    hLne
    (fun ω => empiricalMinkowskiAverage_convex S n
      (fun i _hi ω => hSconv i ω) ω)
    hLconv
    (fun ω => empiricalMinkowskiAverage_radius S hn
      (fun i _hi ω => hRS i ω) ω)
    hRL heps ht N hnet
  intro v hv
  exact empiricalMinkowskiAverage_support_hoeffding_of_radius
    S L v hScompact hSne hLcompact hLne hRS hRL (hN v hv)
    (h_indep v hv) (h_meas v hv) (h_centered v hv) hn ht

/-- Volumetric-net version of the preceding result. It supplies the standard
`(3/eps)^dim` entropy factor and constructs the finite set of directions.-/
theorem exists_hausdorffDist_empiricalMinkowskiAverage_risk_bound_of_hoeffding_net
    {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteDimensional ℝ E]
    (S : ℕ → Ω → Set E) (L : Set E)
    {n : ℕ} (hn : 0 < n) {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (heps_one : eps ≤ 1) (ht : 0 ≤ t)
    (h_indep : ∀ u : E, ‖u‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (h_meas : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_centered : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      μ[directionalSupportDeviation S L u i] = 0) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (N.card : ℝ) ≤ (3 / eps) ^ Module.finrank ℝ E ∧
      μ.real {ω | t + (RS + RL) * eps <
          hausdorffDist (empiricalMinkowskiAverage S n ω) L} ≤
        (3 / eps) ^ Module.finrank ℝ E *
          symmetricSupportHoeffdingTail n t (RS + RL) := by
  apply exists_hausdorffDist_risk_bound_supportFunction_net
    (μ := μ) (fun ω => empiricalMinkowskiAverage S n ω) L
    (fun ω => empiricalMinkowskiAverage_compact S n
      (fun i _hi ω => hScompact i ω) ω)
    hLcompact
    (fun ω => empiricalMinkowskiAverage_nonempty S n
      (fun i _hi ω => hSne i ω) ω)
    hLne
    (fun ω => empiricalMinkowskiAverage_convex S n
      (fun i _hi ω => hSconv i ω) ω)
    hLconv
    (fun ω => empiricalMinkowskiAverage_radius S hn
      (fun i _hi ω => hRS i ω) ω)
    hRL heps heps_one ht
  · unfold symmetricSupportHoeffdingTail
    positivity
  · intro u hu
    exact empiricalMinkowskiAverage_support_hoeffding_of_radius
      S L u hScompact hSne hLcompact hLne hRS hRL hu
      (h_indep u hu) (h_meas u hu) (h_centered u hu) hn ht

/-- Standard closed-form version of the volumetric-net bound. The probability
is bounded by the entropy factor times
`2 exp (-n t² / (2 (RS + RL)²))`.-/
theorem exists_hausdorffDist_empiricalMinkowskiAverage_risk_bound_standard
    {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteDimensional ℝ E]
    (S : ℕ → Ω → Set E) (L : Set E)
    {n : ℕ} (hn : 0 < n) {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hB : 0 < RS + RL)
    (heps : 0 < eps) (heps_one : eps ≤ 1) (ht : 0 ≤ t)
    (h_indep : ∀ u : E, ‖u‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (h_meas : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_centered : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      μ[directionalSupportDeviation S L u i] = 0) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (N.card : ℝ) ≤ (3 / eps) ^ Module.finrank ℝ E ∧
      μ.real {ω | t + (RS + RL) * eps <
          hausdorffDist (empiricalMinkowskiAverage S n ω) L} ≤
        (3 / eps) ^ Module.finrank ℝ E *
          (2 * exp (-(n : ℝ) * t ^ 2 / (2 * (RS + RL) ^ 2))) := by
  obtain ⟨N, hN, hcard, hprob⟩ :=
    exists_hausdorffDist_empiricalMinkowskiAverage_risk_bound_of_hoeffding_net
      (μ := μ) S L hn hScompact hSne hSconv hLcompact hLne hLconv
      hRS hRL heps heps_one ht h_indep h_meas h_centered
  refine ⟨N, hN, hcard, ?_⟩
  rw [symmetricSupportHoeffdingTail_eq_standard hn t hB] at hprob
  exact hprob

/-! ## Exact finite-sample indexing -/

/-- Empirical Minkowski average indexed exactly by the observed sample.-/
def finEmpiricalMinkowskiAverage {n : ℕ}
    (S : Fin n → Ω → Set E) (ω : Ω) : Set E :=
  (n : ℝ)⁻¹ • ∑ i, S i ω

theorem finEmpiricalMinkowskiAverage_compact {n : ℕ}
    (S : Fin n → Ω → Set E) (hS : ∀ i ω, IsCompact (S i ω)) (ω : Ω) :
    IsCompact (finEmpiricalMinkowskiAverage S ω) := by
  unfold finEmpiricalMinkowskiAverage
  apply (isCompact_finset_sum Finset.univ (fun i => S i ω) ?_).smul
  intro i _hi
  exact hS i ω

theorem finEmpiricalMinkowskiAverage_nonempty {n : ℕ}
    (S : Fin n → Ω → Set E) (hS : ∀ i ω, (S i ω).Nonempty) (ω : Ω) :
    (finEmpiricalMinkowskiAverage S ω).Nonempty := by
  unfold finEmpiricalMinkowskiAverage
  exact (nonempty_finset_sum Finset.univ (fun i => S i ω)
    (fun i _hi => hS i ω)).smul_set

theorem finEmpiricalMinkowskiAverage_convex {n : ℕ}
    (S : Fin n → Ω → Set E) (hS : ∀ i ω, Convex ℝ (S i ω)) (ω : Ω) :
    Convex ℝ (finEmpiricalMinkowskiAverage S ω) := by
  unfold finEmpiricalMinkowskiAverage
  apply Convex.smul
  exact convex_sum (fun i => S i ω) (fun i _hi => hS i ω)

/-- A uniform radius is preserved by the exact finite-sample average.-/
theorem finEmpiricalMinkowskiAverage_radius {n : ℕ}
    (S : Fin n → Ω → Set E) (hn : 0 < n) {R : ℝ}
    (hS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ R) (ω : Ω) :
    ∀ x ∈ finEmpiricalMinkowskiAverage S ω, ‖x‖ ≤ R := by
  intro x hx
  unfold finEmpiricalMinkowskiAverage at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Set.mem_finsetSum] at hy
  obtain ⟨g, hg, hsum⟩ := hy
  rw [← hsum, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ * ‖∑ i, g i‖ ≤ (n : ℝ)⁻¹ * ∑ i, ‖g i‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, R := by
      gcongr with i hi
      exact hS i ω (g i) (hg hi)
    _ = R := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- Support functions turn the exact finite Minkowski average into the
ordinary scalar sample average.-/
theorem supportFunction_finEmpiricalMinkowskiAverage
    {n : ℕ} (S : Fin n → Ω → Set E)
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty) (ω : Ω) (u : E) :
    supportFunction (finEmpiricalMinkowskiAverage S ω) u =
      (∑ i, supportFunction (S i ω) u) / (n : ℝ) := by
  unfold finEmpiricalMinkowskiAverage
  rw [supportFunction_smul_set
      (isCompact_finset_sum Finset.univ (fun i => S i ω)
        (fun i _hi => hScompact i ω))
      (nonempty_finset_sum Finset.univ (fun i => S i ω)
        (fun i _hi => hSne i ω))]
  · rw [supportFunction_finset_sum]
    · rw [div_eq_inv_mul]
    · intro i _hi
      exact hScompact i ω
    · intro i _hi
      exact hSne i ω
  · exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Directional support deviation for the exact finite sample family.-/
def finDirectionalSupportDeviation {n : ℕ}
    (S : Fin n → Ω → Set E) (L : Set E) (u : E) (i : Fin n) (ω : Ω) : ℝ :=
  supportFunction (S i ω) u - supportFunction L u

theorem finDirectionalSupportDeviation_mem_Icc_of_radius {n : ℕ}
    (S : Fin n → Ω → Set E) (L : Set E) (u : E) (i : Fin n) (ω : Ω)
    {RS RL : ℝ}
    (hScompact : IsCompact (S i ω)) (hSne : (S i ω).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hRS : ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL) (hu : ‖u‖ ≤ 1) :
    finDirectionalSupportDeviation S L u i ω ∈
      Icc (-(RS + RL)) (RS + RL) := by
  have hS := abs_supportFunction_le_radius hScompact hSne hRS hu
  have hL := abs_supportFunction_le_radius hLcompact hLne hRL hu
  unfold finDirectionalSupportDeviation
  constructor <;>
    linarith [le_abs_self (supportFunction (S i ω) u),
      neg_le_abs (supportFunction (S i ω) u),
      le_abs_self (supportFunction L u), neg_le_abs (supportFunction L u)]

theorem supportFunction_finEmpirical_sub_eq_average_deviation
    {n : ℕ} (S : Fin n → Ω → Set E) (L : Set E) (hn : 0 < n)
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty) (ω : Ω) (u : E) :
    supportFunction (finEmpiricalMinkowskiAverage S ω) u -
        supportFunction L u =
      (∑ i, finDirectionalSupportDeviation S L u i ω) / (n : ℝ) := by
  rw [supportFunction_finEmpiricalMinkowskiAverage S hScompact hSne]
  simp only [finDirectionalSupportDeviation, sum_sub_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- Directional Hoeffding inequality with assumptions only on `Fin n`.-/
theorem finEmpiricalMinkowskiAverage_support_hoeffding
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (S : Fin n → Ω → Set E) (L : Set E) (u : E)
    (a b : Fin n → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun
      (finDirectionalSupportDeviation S L u) μ)
    (h_meas : ∀ i, AEMeasurable
      (finDirectionalSupportDeviation S L u i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ,
      finDirectionalSupportDeviation S L u i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[finDirectionalSupportDeviation S L u i] = 0)
    (hn : 0 < n)
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (finEmpiricalMinkowskiAverage S ω) u -
        supportFunction L u|} ≤
      2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  have htail := ProbabilityTheory.hoeffding_fin_average_abs_real
    (finDirectionalSupportDeviation S L u) a b h_indep h_meas h_bounds
    h_centered hn ht
  have hset :
      {ω | t ≤ |supportFunction (finEmpiricalMinkowskiAverage S ω) u -
        supportFunction L u|} =
      {ω | t ≤ |(∑ i, finDirectionalSupportDeviation S L u i ω) /
        (n : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_finEmpirical_sub_eq_average_deviation
      S L hn hScompact hSne]
  rw [hset]
  exact htail

/-- Radius specialization of finite-sample directional Hoeffding.-/
theorem finEmpiricalMinkowskiAverage_support_hoeffding_of_radius
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (S : Fin n → Ω → Set E) (L : Set E) (u : E)
    {RS RL : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hu : ‖u‖ ≤ 1)
    (h_indep : ProbabilityTheory.iIndepFun
      (finDirectionalSupportDeviation S L u) μ)
    (h_meas : ∀ i, AEMeasurable
      (finDirectionalSupportDeviation S L u i) μ)
    (h_centered : ∀ i,
      μ[finDirectionalSupportDeviation S L u i] = 0)
    (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (finEmpiricalMinkowskiAverage S ω) u -
        supportFunction L u|} ≤
      symmetricSupportHoeffdingTail n t (RS + RL) := by
  have htail := finEmpiricalMinkowskiAverage_support_hoeffding
    S L u (fun _ => -(RS + RL)) (fun _ => RS + RL)
    h_indep h_meas
    (fun i => ae_of_all μ fun ω =>
      finDirectionalSupportDeviation_mem_Icc_of_radius S L u i ω
        (hScompact i ω) (hSne i ω) hLcompact hLne
        (hRS i ω) hRL hu)
    h_centered hn hScompact hSne ht
  simpa only [symmetricSupportHoeffdingTail, sum_const, card_univ,
    Fintype.card_fin, card_range] using htail

/-- Finite-net Hausdorff concentration with probabilistic assumptions only
on the `Fin n` sample.-/
theorem hausdorffDist_finEmpiricalMinkowskiAverage_risk_bound_of_hoeffding
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (S : Fin n → Ω → Set E) (L : Set E) (hn : 0 < n)
    {RS RL eps t : ℝ}
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
      (finDirectionalSupportDeviation S L v) μ)
    (h_meas : ∀ v ∈ N, ∀ i,
      AEMeasurable (finDirectionalSupportDeviation S L v i) μ)
    (h_centered : ∀ v ∈ N, ∀ i,
      μ[finDirectionalSupportDeviation S L v i] = 0) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (finEmpiricalMinkowskiAverage S ω) L} ≤
      N.card * symmetricSupportHoeffdingTail n t (RS + RL) := by
  apply hausdorffDist_risk_bound_of_finset_supportFunction
    (μ := μ) (fun ω => finEmpiricalMinkowskiAverage S ω) L
    (finEmpiricalMinkowskiAverage_compact S hScompact)
    hLcompact
    (finEmpiricalMinkowskiAverage_nonempty S hSne)
    hLne
    (finEmpiricalMinkowskiAverage_convex S hSconv)
    hLconv
    (finEmpiricalMinkowskiAverage_radius S hn hRS)
    hRL heps ht N hnet
  intro v hv
  exact finEmpiricalMinkowskiAverage_support_hoeffding_of_radius
    S L v hScompact hSne hLcompact hLne hRS hRL (hN v hv)
    (h_indep v hv) (h_meas v hv) (h_centered v hv) hn ht

/-- Volumetric-net Hausdorff concentration for an exact `Fin n` sample.-/
theorem exists_hausdorffDist_finEmpiricalMinkowskiAverage_risk_bound_of_hoeffding_net
    {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteDimensional ℝ E]
    {n : ℕ} (S : Fin n → Ω → Set E) (L : Set E) (hn : 0 < n)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (heps_one : eps ≤ 1) (ht : 0 ≤ t)
    (h_indep : ∀ u : E, ‖u‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (finDirectionalSupportDeviation S L u) μ)
    (h_meas : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      AEMeasurable (finDirectionalSupportDeviation S L u i) μ)
    (h_centered : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      μ[finDirectionalSupportDeviation S L u i] = 0) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (N.card : ℝ) ≤ (3 / eps) ^ Module.finrank ℝ E ∧
      μ.real {ω | t + (RS + RL) * eps <
          hausdorffDist (finEmpiricalMinkowskiAverage S ω) L} ≤
        (3 / eps) ^ Module.finrank ℝ E *
          symmetricSupportHoeffdingTail n t (RS + RL) := by
  apply exists_hausdorffDist_risk_bound_supportFunction_net
    (μ := μ) (fun ω => finEmpiricalMinkowskiAverage S ω) L
    (finEmpiricalMinkowskiAverage_compact S hScompact)
    hLcompact
    (finEmpiricalMinkowskiAverage_nonempty S hSne)
    hLne
    (finEmpiricalMinkowskiAverage_convex S hSconv)
    hLconv
    (finEmpiricalMinkowskiAverage_radius S hn hRS)
    hRL heps heps_one ht
  · unfold symmetricSupportHoeffdingTail
    positivity
  · intro u hu
    exact finEmpiricalMinkowskiAverage_support_hoeffding_of_radius
      S L u hScompact hSne hLcompact hLne hRS hRL hu
      (h_indep u hu) (h_meas u hu) (h_centered u hu) hn ht

/-- Closed-form `Fin n` Hausdorff bound with the standard exponent.-/
theorem exists_hausdorffDist_finEmpiricalMinkowskiAverage_risk_bound_standard
    {μ : Measure Ω} [IsProbabilityMeasure μ] [FiniteDimensional ℝ E]
    {n : ℕ} (S : Fin n → Ω → Set E) (L : Set E) (hn : 0 < n)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (hB : 0 < RS + RL)
    (heps : 0 < eps) (heps_one : eps ≤ 1) (ht : 0 ≤ t)
    (h_indep : ∀ u : E, ‖u‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (finDirectionalSupportDeviation S L u) μ)
    (h_meas : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      AEMeasurable (finDirectionalSupportDeviation S L u i) μ)
    (h_centered : ∀ u : E, ‖u‖ ≤ 1 → ∀ i,
      μ[finDirectionalSupportDeviation S L u i] = 0) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (N.card : ℝ) ≤ (3 / eps) ^ Module.finrank ℝ E ∧
      μ.real {ω | t + (RS + RL) * eps <
          hausdorffDist (finEmpiricalMinkowskiAverage S ω) L} ≤
        (3 / eps) ^ Module.finrank ℝ E *
          (2 * exp (-(n : ℝ) * t ^ 2 / (2 * (RS + RL) ^ 2))) := by
  obtain ⟨N, hN, hcard, hprob⟩ :=
    exists_hausdorffDist_finEmpiricalMinkowskiAverage_risk_bound_of_hoeffding_net
      (μ := μ) S L hn hScompact hSne hSconv hLcompact hLne hLconv
      hRS hRL heps heps_one ht h_indep h_meas h_centered
  refine ⟨N, hN, hcard, ?_⟩
  rw [symmetricSupportHoeffdingTail_eq_standard hn t hB] at hprob
  exact hprob

end RandomSetTheory.Empirical
