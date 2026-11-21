/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Probability.Moments.SubGaussian
import Tengoku.Seed.Probability.StrongLaw
import Tengoku.Seed.MeasureTheory.Covering.BesicovitchVectorSpace
import Tengoku.Seed.Topology.MetricSpace.CoveringNumbers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-net concentration tools

This module reuses Mathlib's sub-Gaussian theory and adds a minimal sub-gamma
interface for Bernstein bounds. All measurability, independence, and
integrability assumptions are explicit.
-/

open Real Set Filter Finset Module
open MeasureTheory
open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal Function

namespace ProbabilityTheory

open Metric

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Markov exponentiel/Chernoff, écrit directement avec une intégrale.
@isnad1 id=le.2h5v.s7.5192482667f5 from=translated src=- shape=258758d9 vocab=dd6d8bab
-/
lemma exponential_markov_real [IsFiniteMeasure μ]
    (X : Ω → ℝ) (q t : ℝ) (hq : 0 ≤ q)
    (h_exp : Integrable (fun ω => exp (q * X ω)) μ) :
    μ.real {ω | t ≤ X ω} ≤ (∫ ω, exp (q * X ω) ∂μ) / exp (q * t) := by
  calc
    μ.real {ω | t ≤ X ω} ≤ exp (-q * t) * mgf X μ q :=
      measure_ge_le_exp_mul_mgf t hq h_exp
    _ = (∫ ω, exp (q * X ω) ∂μ) / exp (q * t) := by
      rw [mgf, div_eq_mul_inv, ← exp_neg]
      ring

/-- Hoeffding pour une somme finie de variables indépendantes, centrées et bornées.
@isnad1 id=le.5h8v.s8.8897315aa6a7 from=translated src=- shape=56fbeed1 vocab=879f8109
-/
lemma hoeffding_sum_real [IsProbabilityMeasure μ]
    {ι : Type*} (X : ι → Ω → ℝ) (a b : ι → ℝ)
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

/-- Forme moyenne empirique de l'inégalité de Hoeffding.
@isnad1 id=le.6h7v.s8.85536c253944 from=translated src=- shape=3c9447dd vocab=21a25cb9
-/
lemma hoeffding_average_real [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ i ∈ range n, X i ω) / (n : ℝ)} ≤
      exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  have h := hoeffding_sum_real X a b h_indep h_meas h_bounds h_centered
    (range n) (mul_nonneg (Nat.cast_nonneg n) ht)
  have hset : {ω | t ≤ (∑ i ∈ range n, X i ω) / (n : ℝ)} =
      {ω | (n : ℝ) * t ≤ ∑ i ∈ range n, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [le_div_iff₀ (Nat.cast_pos.mpr hn)]
    ring
  rw [hset]
  exact h

/-- Version bilatérale de Hoeffding pour une moyenne empirique.
@isnad1 id=le.6h7v.s8.6250227530d2 from=translated src=- shape=1082e61b vocab=4db4ac76
-/
lemma hoeffding_average_abs_real [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ i, μ[X i] = 0)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i ∈ range n, X i ω) / (n : ℝ)|} ≤
      2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
  let Xneg : ℕ → Ω → ℝ := fun i ω => -X i ω
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
  have hpos := hoeffding_average_real X a b h_indep h_meas h_bounds h_centered hn ht
  have hneg := hoeffding_average_real Xneg (-b) (-a) h_indep_neg h_meas_neg
    h_bounds_neg h_centered_neg hn ht
  have hset : {ω | t ≤ |(∑ i ∈ range n, X i ω) / (n : ℝ)|} =
      {ω | t ≤ (∑ i ∈ range n, X i ω) / (n : ℝ)} ∪
      {ω | t ≤ (∑ i ∈ range n, Xneg i ω) / (n : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Xneg]
    rw [show (∑ i ∈ range n, -X i ω) = -(∑ i ∈ range n, X i ω) by simp]
    rw [neg_div, le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | t ≤ (∑ i ∈ range n, X i ω) / (n : ℝ)} +
        μ.real {ω | t ≤ (∑ i ∈ range n, Xneg i ω) / (n : ℝ)} :=
      measureReal_union_le _ _
    _ ≤ exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) +
        exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      apply add_le_add hpos
      simpa [Xneg, sub_eq_add_neg, add_comm] using hneg
    _ = 2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
          (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ))) := by
      ring

/-- Union bound réelle sur une famille finie d'événements.
@isnad1 id=le.1h6v.s6.9bf6bdcb6637 from=translated src=- shape=d10edb30 vocab=7d435907
-/
lemma measureReal_biUnion_finset_le_card_mul {ι : Type*} [IsFiniteMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) {q : ℝ}
    (hA : ∀ i ∈ s, μ.real (A i) ≤ q) :
    μ.real (⋃ i ∈ s, A i) ≤ s.card * q := by
  calc
    μ.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.real (A i) :=
      measureReal_biUnion_finset_le s A
    _ ≤ ∑ _i ∈ s, q := Finset.sum_le_sum fun i hi => hA i hi
    _ = s.card * q := by simp

/-- Union bound sous la forme utilisée pour un réseau fini de directions.
@isnad1 id=le.1h7v.s6.4e02845c9ed8 from=translated src=- shape=fc38aee3 vocab=5d1a1463
-/
lemma finite_family_deviation_bound {ι : Type*} [IsFiniteMeasure μ]
    (s : Finset ι) (Z : ι → Ω → ℝ) {t q : ℝ}
    (htail : ∀ i ∈ s, μ.real {ω | t ≤ |Z i ω|} ≤ q) :
    μ.real {ω | ∃ i ∈ s, t ≤ |Z i ω|} ≤ s.card * q := by
  have hset : {ω | ∃ i ∈ s, t ≤ |Z i ω|} =
      ⋃ i ∈ s, {ω | t ≤ |Z i ω|} := by
    ext ω
    simp
  rw [hset]
  exact measureReal_biUnion_finset_le_card_mul s _ htail

/-- Uniform Hoeffding bound over a finite family.
@isnad1 id=le.6h9v.s8.b2af942febe4 from=translated src=- shape=c56d165a vocab=7dbf6b96
-/
lemma finite_family_hoeffding_average_abs {ι : Type*} [IsProbabilityMeasure μ]
    (s : Finset ι) (X : ι → ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (h_indep : ∀ u ∈ s, iIndepFun (X u) μ)
    (h_meas : ∀ u ∈ s, ∀ i, AEMeasurable (X u i) μ)
    (h_bounds : ∀ u ∈ s, ∀ i, ∀ᵐ ω ∂μ, X u i ω ∈ Icc (a i) (b i))
    (h_centered : ∀ u ∈ s, ∀ i, μ[X u i] = 0)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ u ∈ s, t ≤ |(∑ i ∈ range n, X u i ω) / (n : ℝ)|} ≤
      s.card * (2 * exp (-((n : ℝ) * t) ^ 2 / (2 * (↑(∑ i ∈ range n,
        (((‖b i - a i‖₊ / (2 : NNReal)) ^ (2 : ℕ)) : NNReal) : NNReal) : ℝ)))) := by
  apply finite_family_deviation_bound s
    (fun u ω => (∑ i ∈ range n, X u i ω) / (n : ℝ))
  intro u hu
  exact hoeffding_average_abs_real (X u) a b (h_indep u hu) (h_meas u hu)
    (h_bounds u hu) (h_centered u hu) hn ht

omit [MeasurableSpace Ω] in
/-- Passage déterministe d'un réseau fini au supremum sur tout l'ensemble de directions.
@isnad1 id=le.3h8v.s7.ca818fc472c2 from=translated src=- shape=fe4c0f7a vocab=0f229acb
-/
lemma finiteNet_deviation_subset {E : Type*} [PseudoMetricSpace E]
    (D : Set E) (N : Finset E) {ε L s : ℝ} (hL : 0 ≤ L)
    (hnet : ∀ u ∈ D, ∃ v ∈ N, dist u v ≤ ε)
    (Z : Ω → E → ℝ)
    (hLip : ∀ ω u, u ∈ D → ∀ v, v ∈ N →
      |Z ω u - Z ω v| ≤ L * dist u v) :
    {ω | ∃ u ∈ D, s + L * ε < |Z ω u|} ⊆
      {ω | ∃ v ∈ N, s < |Z ω v|} := by
  rintro ω ⟨u, hu, hlarge⟩
  obtain ⟨v, hv, huv⟩ := hnet u hu
  refine ⟨v, hv, ?_⟩
  by_contra hsmall
  have hvle : |Z ω v| ≤ s := le_of_not_gt hsmall
  have htri : |Z ω u| ≤ |Z ω v| + |Z ω u - Z ω v| := by
    calc
      |Z ω u| = |(Z ω u - Z ω v) + Z ω v| := by ring_nf
      _ ≤ |Z ω u - Z ω v| + |Z ω v| := abs_add_le _ _
      _ = |Z ω v| + |Z ω u - Z ω v| := add_comm _ _
  have hlip := hLip ω u hu v hv
  have hmul : L * dist u v ≤ L * ε := mul_le_mul_of_nonneg_left huv hL
  linarith

/-- Borne probabiliste uniforme obtenue à partir d'un réseau fini et d'un module Lipschitz.
@isnad1 id=le.4h10v.s8.b640ef80f241 from=translated src=- shape=6ddbe90b vocab=81bf0850
-/
lemma finiteNet_uniform_deviation_bound {E : Type*} [PseudoMetricSpace E]
    [IsFiniteMeasure μ] (D : Set E) (N : Finset E) {ε L s q : ℝ} (hL : 0 ≤ L)
    (hnet : ∀ u ∈ D, ∃ v ∈ N, dist u v ≤ ε)
    (Z : Ω → E → ℝ)
    (hLip : ∀ ω u, u ∈ D → ∀ v, v ∈ N →
      |Z ω u - Z ω v| ≤ L * dist u v)
    (htail : ∀ v ∈ N, μ.real {ω | s ≤ |Z ω v|} ≤ q) :
    μ.real {ω | ∃ u ∈ D, s + L * ε < |Z ω u|} ≤ N.card * q := by
  calc
    μ.real {ω | ∃ u ∈ D, s + L * ε < |Z ω u|} ≤
        μ.real {ω | ∃ v ∈ N, s ≤ |Z ω v|} := by
      apply measureReal_mono _ (by finiteness)
      exact (finiteNet_deviation_subset D N hL hnet Z hLip).trans
        (by rintro ω ⟨v, hv, hstrict⟩; exact ⟨v, hv, hstrict.le⟩)
    _ ≤ N.card * q :=
      finite_family_deviation_bound (μ := μ) N (fun v ω => Z ω v)
        (t := s) (q := q) htail

/-- Un compact admet un réseau fini interne à toute précision strictement positive.
@isnad1 id=ex.2h3v.s6.6e36b0817cd8 from=translated src=- shape=a3b8a371 vocab=30854ff8
-/
lemma compact_exists_finset_net {E : Type*} [PseudoMetricSpace E]
    (D : Set E) (hD : IsCompact D) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E,
      (∀ v ∈ N, v ∈ D) ∧
      (∀ u ∈ D, ∃ v ∈ N, dist u v ≤ ε) := by
  obtain ⟨T, hTD, hTfinite, hcover⟩ := finite_cover_balls_of_compact hD hε
  classical
  refine ⟨hTfinite.toFinset, ?_, ?_⟩
  · intro v hv
    exact hTD (by simpa using hv)
  · intro u hu
    have hucover := hcover hu
    simp only [mem_iUnion, Metric.mem_ball] at hucover
    obtain ⟨v, hvT, huv⟩ := hucover
    exact ⟨v, by simpa using hvT, huv.le⟩

section EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
Argument volumique pour une famille finie `eps`-séparée dans une boule de norme.
Cette forme `ENNReal` est l'étape robuste qui annule le volume de la boule unité.
@isnad1 id=le.3h4v.s8.32e930a2b7ed from=translated src=- shape=9c3bec11 vocab=e5f3bef9
-/
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
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
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
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
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

/-- Forme réelle de l'estimation volumique de packing.
@isnad1 id=le.4h4v.s8.bbff8b0a1fb6 from=translated src=- shape=24b42c37 vocab=876eb2c7
-/
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

/--
Dans la boule unité, une famille finie `eps`-séparée a au plus
`(1 + 2 / eps) ^ finrank ℝ E` points.
@isnad1 id=le.3h3v.s7.3fb7a51056cd from=translated src=- shape=0180cdde vocab=876eb2c7
-/
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

end EuclideanNets

/-- Tout ensemble compact a un nombre de packing fini à rayon strictement positif.
@isnad1 id=ne.2h3v.s5.baaac306e1d2 from=translated src=- shape=19567667 vocab=c9694eef
-/
theorem packingNumber_ne_top_of_isCompact {E : Type*} [PseudoMetricSpace E]
    (D : Set E) (hD : IsCompact D) {eps : ℝ≥0} (heps : 0 < eps) :
    Metric.packingNumber eps D ≠ ⊤ := by
  obtain ⟨N, _hND, hnet⟩ := compact_exists_finset_net D hD
    (show 0 < (eps : ℝ) / 2 by positivity)
  have hcover : Metric.IsCover (eps / 2) D (N : Set E) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    refine ⟨y, by simpa using hy, ?_⟩
    change edist x y ≤ (eps / 2 : ℝ≥0)
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    simpa using hxy
  have hext : Metric.externalCoveringNumber (eps / 2) D ≤ (N : Set E).encard :=
    hcover.externalCoveringNumber_le_encard
  have hpack : Metric.packingNumber eps D ≤ (N : Set E).encard := by
    have h := (Metric.packingNumber_two_mul_le_externalCoveringNumber (eps / 2) D).trans hext
    have heq : 2 * (eps / 2) = eps := by field_simp
    rwa [heq] at h
  exact ne_top_of_le_ne_top (by simp) hpack

section EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
Filet fini interne de la boule unité avec la borne volumique standard
`(1 + 2 / eps) ^ finrank ℝ E`.
@isnad1 id=ex.1h2v.s7.3ad146c5a1be from=translated src=- shape=43a18c24 vocab=5b044614
-/
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
    have huD : u ∈ D := by simpa [D, mem_closedBall, dist_zero_right] using hu
    obtain ⟨v, hvC, huv⟩ := Metric.isCover_maximalSeparatedSet htop huD
    have hvN : v ∈ (N : Set E) := hNC.symm ▸ hvC
    refine ⟨v, by simpa using hvN, ?_⟩
    change edist u v ≤ (epsNN : ℝ≥0∞) at huv
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at huv
    change ENNReal.ofReal (dist u v) ≤ ENNReal.ofReal eps at huv
    exact (ENNReal.ofReal_le_ofReal_iff heps.le).mp huv
  refine ⟨N, hNmem, hNcover, ?_⟩
  exact finset_card_le_one_add_two_div_pow N heps hNmem hNsep

/-- Pour `eps ≤ 1`, la borne usuelle simplifiée `(3 / eps) ^ finrank ℝ E`.
@isnad1 id=ex.2h2v.s7.b9dc2b0be50d from=translated src=- shape=02ab53e8 vocab=bd620544
-/
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

end EuclideanNets

/--
Version compacte du passage au réseau : le réseau fini est construit à
l'intérieur de `D`, puis la borne de queue ponctuelle est union-bornée.
@isnad1 id=ex.5h9v.s8.ca9aeda84485 from=translated src=- shape=ef6b5dfe vocab=d520ca7a
-/
lemma compact_uniform_deviation_bound {E : Type*} [PseudoMetricSpace E]
    [IsFiniteMeasure μ] (D : Set E) (hD : IsCompact D)
    {ε L s q : ℝ} (hε : 0 < ε) (hL : 0 ≤ L)
    (Z : Ω → E → ℝ)
    (hLip : ∀ ω u, u ∈ D → ∀ v, v ∈ D →
      |Z ω u - Z ω v| ≤ L * dist u v)
    (htail : ∀ v ∈ D, μ.real {ω | s ≤ |Z ω v|} ≤ q) :
    ∃ N : Finset E,
      (∀ v ∈ N, v ∈ D) ∧
      μ.real {ω | ∃ u ∈ D, s + L * ε < |Z ω u|} ≤ N.card * q := by
  obtain ⟨N, hND, hnet⟩ := compact_exists_finset_net D hD hε
  refine ⟨N, hND, finiteNet_uniform_deviation_bound D N hL hnet Z ?_ ?_⟩
  · intro ω u hu v hv
    exact hLip ω u hu v (hND v hv)
  · intro v hv
    exact htail v (hND v hv)

/-- Loi forte des grands nombres pour une suite i.i.d. réelle intégrable.
@isnad1 id=eventual.3h3v.s7.b76aee49b65d from=translated src=- shape=d37628da vocab=dd73d7d2
-/
lemma strong_law_ae_of_iIndepFun
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (h_indep : iIndepFun X μ)
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0]) := by
  apply strong_law_ae_real X hint
  · exact fun _i _j hij => h_indep.indepFun hij
  · exact h_ident

/-- Contrôle unilatéral sub-gamma de la fonction génératrice des moments.

Cette interface est suffisante pour obtenir Bernstein sans développer toute
la théorie des normes d'Orlicz `ψ₁`.-/
structure HasSubgammaMGF (X : Ω → ℝ) (v c : ℝ) (μ : Measure Ω) : Prop where
  v_nonneg : 0 ≤ v
  c_nonneg : 0 ≤ c
  integrable_exp_mul : ∀ q : ℝ, 0 ≤ q → c * q < 1 →
    Integrable (fun ω => exp (q * X ω)) μ
  mgf_le : ∀ q : ℝ, 0 ≤ q → c * q < 1 →
    mgf X μ q ≤ exp (v * q ^ 2 / (2 * (1 - c * q)))

/-- Les variances-proxy de variables sub-gamma indépendantes s'additionnent.
@isnad1 id=hassubga.4h7v.s6.9a4a08451035 from=translated src=- shape=44e84315 vocab=6e191ea4
-/
lemma HasSubgammaMGF.sum_of_iIndepFun [IsFiniteMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {v : ι → ℝ} {c : ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (hc : 0 ≤ c) (s : Finset ι) (h : ∀ i ∈ s, HasSubgammaMGF (X i) (v i) c μ) :
    HasSubgammaMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) c μ where
  v_nonneg := Finset.sum_nonneg fun i hi => (h i hi).v_nonneg
  c_nonneg := hc
  integrable_exp_mul q hq hcq := by
    simpa only [Finset.sum_apply] using
      h_indep.integrable_exp_mul_sum h_meas
        (fun i hi => (h i hi).integrable_exp_mul q hq hcq)
  mgf_le q hq hcq := by
    rw [show (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i by ext; simp,
      h_indep.mgf_sum h_meas s]
    calc
      ∏ i ∈ s, mgf (X i) μ q ≤
          ∏ i ∈ s, exp (v i * q ^ 2 / (2 * (1 - c * q))) := by
        exact Finset.prod_le_prod (fun _i _hi => mgf_nonneg)
          (fun i hi => (h i hi).mgf_le q hq hcq)
      _ = exp ((∑ i ∈ s, v i) * q ^ 2 / (2 * (1 - c * q))) := by
        rw [← exp_sum]
        congr 1
        rw [← Finset.sum_div, ← Finset.sum_mul]

/-- Borne de Bernstein à droite obtenue à partir d'un contrôle sub-gamma.
@isnad1 id=le.3h6v.s7.d7ae9d0156d7 from=translated src=- shape=6f873372 vocab=21410212
-/
lemma HasSubgammaMGF.measure_ge_le [IsFiniteMeasure μ]
    {X : Ω → ℝ} {v c : ℝ} (h : HasSubgammaMGF X v c μ)
    (hv : 0 < v) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * (v + c * ε))) := by
  let q := ε / (v + c * ε)
  have hden : 0 < v + c * ε := by
    nlinarith [mul_nonneg h.c_nonneg hε]
  have hq : 0 ≤ q := div_nonneg hε hden.le
  have hcq : c * q < 1 := by
    dsimp [q]
    calc
      c * (ε / (v + c * ε)) = (c * ε) / (v + c * ε) := by ring
      _ < 1 := (div_lt_one hden).2 (by linarith)
  have hone_eq : 1 - c * q = v / (v + c * ε) := by
    dsimp [q]
    field_simp [ne_of_gt hden]
    ring
  calc
    μ.real {ω | ε ≤ X ω} ≤ exp (-q * ε) * mgf X μ q :=
      measure_ge_le_exp_mul_mgf ε hq (h.integrable_exp_mul q hq hcq)
    _ ≤ exp (-q * ε) * exp (v * q ^ 2 / (2 * (1 - c * q))) := by
      gcongr
      exact h.mgf_le q hq hcq
    _ = exp (-ε ^ 2 / (2 * (v + c * ε))) := by
      rw [← exp_add]
      congr 1
      rw [hone_eq]
      dsimp [q]
      field_simp [ne_of_gt hv, ne_of_gt hden]
      ring

/-- Contrôle sub-gamma symétrique, utilisable comme interface sub-exponentielle.-/
structure HasTwoSidedSubgammaMGF (X : Ω → ℝ) (v c : ℝ) (μ : Measure Ω) : Prop where
  pos : HasSubgammaMGF X v c μ
  neg : HasSubgammaMGF (-X) v c μ

/-- Une somme de variables sub-gamma bilatérales indépendantes reste sub-gamma bilatérale.
@isnad1 id=hastwosi.4h7v.s6.8a607910e7cc from=translated src=- shape=44e84315 vocab=8befb064
-/
lemma HasTwoSidedSubgammaMGF.sum_of_iIndepFun [IsFiniteMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {v : ι → ℝ} {c : ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (hc : 0 ≤ c) (s : Finset ι) (h : ∀ i ∈ s, HasTwoSidedSubgammaMGF (X i) (v i) c μ) :
    HasTwoSidedSubgammaMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) c μ where
  pos := HasSubgammaMGF.sum_of_iIndepFun h_indep h_meas hc s fun i hi => (h i hi).pos
  neg := by
    have h_indep_neg : iIndepFun (fun i => -X i) μ := by
      exact (h_indep.comp (fun _i => fun x : ℝ => -x) (fun _i => measurable_neg)).congr
        (fun _i => ae_of_all μ fun _ω => rfl)
    have h_neg := HasSubgammaMGF.sum_of_iIndepFun h_indep_neg
      (fun i => (h_meas i).neg) hc s (fun i hi => (h i hi).neg)
    change HasSubgammaMGF (fun ω => -(∑ i ∈ s, X i ω)) (∑ i ∈ s, v i) c μ
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using h_neg

/-- Borne de Bernstein bilatérale.
@isnad1 id=le.3h6v.s7.02740ea05b16 from=translated src=- shape=76b15d25 vocab=e1a6e255
-/
lemma HasTwoSidedSubgammaMGF.measure_abs_ge_le [IsFiniteMeasure μ]
    {X : Ω → ℝ} {v c : ℝ} (h : HasTwoSidedSubgammaMGF X v c μ)
    (hv : 0 < v) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * (v + c * ε))) := by
  have hset : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Pi.neg_apply, le_abs]
  rw [hset]
  calc
    μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) ≤
        μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ (-X) ω} :=
      measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * (v + c * ε))) +
        exp (-ε ^ 2 / (2 * (v + c * ε))) :=
      add_le_add (h.pos.measure_ge_le hv hε) (h.neg.measure_ge_le hv hε)
    _ = 2 * exp (-ε ^ 2 / (2 * (v + c * ε))) := by ring

end ProbabilityTheory
