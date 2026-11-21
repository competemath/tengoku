/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.L2LipschitzEmpiricalProcess
import Tengoku.Randomsettheory.RandomSetTheory.PolynomialSupportChaining
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanChainingNets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Euclidean chaining for a truncated `L²` empirical process

This file connects the scalar bounded-variance Bernstein estimate to the
countable Euclidean chaining machinery.  The process is anchored at a fixed
index.  Anchoring makes its value at zero automatic and avoids any separate
integrability assumption on the absolute level of the observation process.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology
open RandomSetTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega Z T iota : Type*} [MeasurableSpace Omega] [MeasurableSpace Z]
  [PseudoMetricSpace T] {mu : Measure Omega}

/-- A truncated empirical process centered at a fixed index `o`.-/
def centeredAnchoredTruncatedEmpiricalProcess
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : iota → Omega → Z) (I : Finset iota) (o : T)
    (omega : Omega) (t : T) : ℝ :=
  c * ∑ i ∈ I,
    (truncatedLipschitzIncrement H R M X i t o omega -
      ∫ xi, truncatedLipschitzIncrement H R M X i t o xi ∂mu)

/-- The expectation of a truncated anchored increment is Lipschitz in its
free index, with the same deterministic truncation constant.
@isnad1 id=lipschit.6h11v.s7.6323aa9480ce from=translated src=- shape=a49041e1 vocab=87660f6f
-/
theorem lipschitzWith_integral_truncatedLipschitzIncrement
    [IsProbabilityMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (i : iota) (o : T) :
    LipschitzWith (Real.toNNReal M)
      (fun t ↦ ∫ xi, truncatedLipschitzIncrement H R M X i t o xi ∂mu) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hs := integrable_truncatedLipschitzIncrement
    (μ := mu) H R hM X hX hH hRmeas hR hLip i s o
  have ht := integrable_truncatedLipschitzIncrement
    (μ := mu) H R hM X hX hH hRmeas hR hLip i t o
  rw [Real.dist_eq, ← integral_sub hs ht]
  have hbound : ∀ᵐ xi ∂mu,
      ‖truncatedLipschitzIncrement H R M X i s o xi -
          truncatedLipschitzIncrement H R M X i t o xi‖ ≤
        M * dist s t := by
    filter_upwards with xi
    have hst := abs_truncatedLipschitzObservation_sub_le
      H R hM hR hLip (X i xi) s t
    rw [Real.norm_eq_abs]
    convert hst using 1
    unfold truncatedLipschitzIncrement
    ring
  have hint := norm_integral_le_of_norm_le_const hbound
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one,
    Real.coe_toNNReal _ hM] using hint

/-- Continuity of one sample path of the anchored truncated process.
@isnad1 id=continuo.7h13v.s7.a3c7ba7ee3d9 from=translated src=- shape=53bbca8c vocab=2ebc4b7f
-/
theorem continuous_centeredAnchoredTruncatedEmpiricalProcess
    [IsProbabilityMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M c : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (I : Finset iota) (o : T) (omega : Omega) :
    Continuous
      (centeredAnchoredTruncatedEmpiricalProcess
        (mu := mu) H R M c X I o omega) := by
  unfold centeredAnchoredTruncatedEmpiricalProcess
  apply continuous_const.mul
  apply continuous_finsetSum I
  intro i hi
  apply Continuous.sub
  · unfold truncatedLipschitzIncrement truncatedLipschitzObservation
    by_cases hz : R (X i omega) ≤ M
    · simp only [ite_eq_left hz]
      exact (hHcont (X i omega)).sub continuous_const
    · simp only [ite_eq_right hz]
      fun_prop
  · exact (lipschitzWith_integral_truncatedLipschitzIncrement
      (mu := mu) H R hM X hX hHmeas hRmeas hR hLip i o).continuous

/-- Algebraic increment identity for the anchored process.
@isnad1 id=eq.6h15v.s8.93cdd1e60699 from=translated src=- shape=301bdb37 vocab=13c48229
-/
theorem centeredAnchoredTruncatedEmpiricalProcess_sub
    [IsProbabilityMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M c : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hRmeas : Measurable R) (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (I : Finset iota) (o : T) (omega : Omega) (s t : T) :
    centeredAnchoredTruncatedEmpiricalProcess
          (mu := mu) H R M c X I o omega s -
        centeredAnchoredTruncatedEmpiricalProcess
          (mu := mu) H R M c X I o omega t =
      c * ∑ i ∈ I,
        (truncatedLipschitzIncrement H R M X i s t omega -
          ∫ xi, truncatedLipschitzIncrement H R M X i s t xi ∂mu) := by
  unfold centeredAnchoredTruncatedEmpiricalProcess
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hs := integrable_truncatedLipschitzIncrement
    (μ := mu) H R hM X hX hHmeas hRmeas hR hLip i s o
  have ht := integrable_truncatedLipschitzIncrement
    (μ := mu) H R hM X hX hHmeas hRmeas hR hLip i t o
  have hpoint :
      truncatedLipschitzIncrement H R M X i s o omega -
          truncatedLipschitzIncrement H R M X i t o omega =
        truncatedLipschitzIncrement H R M X i s t omega := by
    unfold truncatedLipschitzIncrement
    ring
  have hint :
      (∫ xi, truncatedLipschitzIncrement H R M X i s o xi ∂mu) -
          ∫ xi, truncatedLipschitzIncrement H R M X i t o xi ∂mu =
        ∫ xi, truncatedLipschitzIncrement H R M X i s t xi ∂mu := by
    rw [← integral_sub hs ht]
    apply integral_congr_ae
    filter_upwards with xi
    unfold truncatedLipschitzIncrement
    ring
  calc
    _ = (truncatedLipschitzIncrement H R M X i s o omega -
          truncatedLipschitzIncrement H R M X i t o omega) -
        ((∫ xi, truncatedLipschitzIncrement H R M X i s o xi ∂mu) -
          ∫ xi, truncatedLipschitzIncrement H R M X i t o xi ∂mu) := by ring
    _ = _ := by rw [hpoint, hint]

/-- The anchored process vanishes at its anchor.
@isnad1 id=eq.0h13v.s6.2c09245ca1e9 from=translated src=- shape=310b4621 vocab=f85d2baa
-/
@[simp]
theorem centeredAnchoredTruncatedEmpiricalProcess_anchor
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : iota → Omega → Z) (I : Finset iota) (o : T) (omega : Omega) :
    centeredAnchoredTruncatedEmpiricalProcess
      (mu := mu) H R M c X I o omega o = 0 := by
  simp [centeredAnchoredTruncatedEmpiricalProcess,
    truncatedLipschitzIncrement]

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A linearly growing confidence budget still gives a vanishing (indeed
summable) mixed-process radius at dyadic spatial scales.
@isnad1 id=summable.1h4v.s6.f5c9873135f6 from=translated src=- shape=c0debe62 vocab=020ce47f
-/
theorem summable_dyadic_mixedEuclideanProcessBound
    (sigma2 sigma1 : ℝ) (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun k ↦ mixedEuclideanProcessBound
      (((1 / 2 : ℝ) ^ k) * sigma2)
      (((1 / 2 : ℝ) ^ k) * sigma1) d
      (mixedEuclideanConfidence d x k)) := by
  let q : ℝ := 1 / 2
  have hq : ‖q‖ < 1 := by norm_num [q, Real.norm_eq_abs]
  have hgeom : Summable (fun k : ℕ ↦ q ^ k) :=
    summable_geometric_of_norm_lt_one hq
  have hthresholdSqrt :=
    summable_mixedEuclideanThreshold
      (σ₂ := (1 : ℝ)) (σ₁ := (0 : ℝ))
      (by norm_num) (by norm_num) d hx
  have hsqrt : Summable (fun k : ℕ ↦
      q ^ k * Real.sqrt (2 * mixedEuclideanConfidence d x k)) := by
    have h := hthresholdSqrt.mul_left (1 / 3 : ℝ)
    simpa [mixedEuclideanThreshold, q, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hthresholdLinear :=
    summable_mixedEuclideanThreshold
      (σ₂ := (0 : ℝ)) (σ₁ := (1 : ℝ))
      (by norm_num) (by norm_num) d hx
  have hlinear : Summable (fun k : ℕ ↦
      q ^ k * mixedEuclideanConfidence d x k) := by
    have h := hthresholdLinear.mul_left (1 / 6 : ℝ)
    simpa [mixedEuclideanThreshold, q, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hsum :=
    (((hsqrt.mul_left (6 * sigma2)).add
      (hgeom.mul_left (72 * sigma2 * Real.sqrt (d + 1 : ℝ)))).add
      (hlinear.mul_left (12 * sigma1))).add
      (hgeom.mul_left (144 * sigma1 * (d + 1 : ℝ)))
  simpa [mixedEuclideanProcessBound, q, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- A single volumetric net at dyadic resolution is dominated by the loose
entropy budget used by the mixed chaining construction.
@isnad1 id=le.0h2v.s6.8a4f23143677 from=translated src=- shape=2cab1069 vocab=558d4ae8
-/
theorem one_add_two_div_dyadicResolution_pow_le_exp
    (d k : ℕ) :
    (1 + 2 / RandomSetTheory.dyadicResolution k) ^ d ≤
      Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) := by
  have hdelta := RandomSetTheory.dyadicResolution_pos k
  have hdeltaOne := RandomSetTheory.dyadicResolution_le_one k
  have hbase :
      1 + 2 / RandomSetTheory.dyadicResolution k ≤
        3 / RandomSetTheory.dyadicResolution k := by
    apply (le_div_iff₀ hdelta).2
    calc
      (1 + 2 / RandomSetTheory.dyadicResolution k) *
          RandomSetTheory.dyadicResolution k =
        RandomSetTheory.dyadicResolution k + 2 := by field_simp
      _ ≤ 3 := by linarith
  have hpow :
      (1 + 2 / RandomSetTheory.dyadicResolution k) ^ d ≤
        (3 / RandomSetTheory.dyadicResolution k) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have hexpBase := RandomSetTheory.three_div_dyadicResolution_le_exp k
  calc
    (1 + 2 / RandomSetTheory.dyadicResolution k) ^ d ≤
        (3 / RandomSetTheory.dyadicResolution k) ^ d := hpow
    _ ≤ (Real.exp (2 * (k + 1 : ℝ))) ^ d :=
      pow_le_pow_left₀ (by positivity) hexpBase d
    _ = Real.exp ((d : ℝ) * (2 * (k + 1 : ℝ))) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) := by
      rw [Real.exp_le_exp]
      nlinarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d,
        show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]

/-- Uniform chaining bound for the centered truncated process on a Euclidean
unit ball.  Crucially, its constants do not depend on the sample size.
@isnad1 id=other.12h11v.s9.2b289111aea5 from=translated src=- shape=482d0225 vocab=c6628c32
-/
theorem measureReal_unitBall_range_succ_centeredTruncated_largeDeviation_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a K x : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K) (hx : 0 ≤ x)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) :
    let G : Omega → EuclideanUnitBall E → ℝ := fun omega t ↦
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega (t : E)
    mu.real {omega | ∃ t : EuclideanUnitBall E,
      mixedEuclideanProcessBound (2 * K) (2 * a) (finrank ℝ E) x <
        |G omega t|} ≤ Real.exp (-x) := by
  dsimp only
  let G : Omega → EuclideanUnitBall E → ℝ := fun omega t ↦
    centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
      (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
      (Finset.range (n + 1)) 0 omega (t : E)
  apply measureReal_unitBall_mixedProcess_largeDeviation_le
    G (by positivity) (by positivity) hx
  · intro omega
    exact (continuous_centeredAnchoredTruncatedEmpiricalProcess
      H R (mul_nonneg ha (Real.sqrt_nonneg _)) X hX hHmeas hHcont
        hRmeas hR hLip (Finset.range (n + 1)) 0 omega).comp
          continuous_subtype_val
  · intro omega
    exact centeredAnchoredTruncatedEmpiricalProcess_anchor
      H R _ _ X (Finset.range (n + 1)) 0 omega
  · intro s t y hy
    have htail :=
      measureReal_range_succ_centeredTruncated_increment_mixedTail
        H R ha hK X hX hIndep hHmeas hRmeas hR hLip hRL2 hRsecond
          n (s : E) (t : E) y hy
    have hsub : ∀ omega, G omega s - G omega t =
        (Real.sqrt (n + 1 : ℝ))⁻¹ * ∑ i ∈ Finset.range (n + 1),
          (truncatedLipschitzIncrement H R
              (a * Real.sqrt (n + 1 : ℝ)) X i (s : E) (t : E) omega -
            ∫ xi, truncatedLipschitzIncrement H R
              (a * Real.sqrt (n + 1 : ℝ)) X i (s : E) (t : E) xi ∂mu) := by
      intro omega
      exact centeredAnchoredTruncatedEmpiricalProcess_sub
        H R (mul_nonneg ha (Real.sqrt_nonneg _)) X hX hHmeas hRmeas
          hR hLip (Finset.range (n + 1)) 0 omega (s : E) (t : E)
    simpa only [G, hsub, Subtype.dist_eq] using htail

/-- The same chaining estimate after translating the index set by `u` and
scaling it by `r`.  This is the local-oscillation input used in the tightness
argument.  The variance and Bernstein scales both contract linearly with the
radius.
@isnad1 id=other.13h13v.s9.aa4be28db775 from=translated src=- shape=9b6a1805 vocab=96dc227b
-/
theorem measureReal_unitBall_local_range_succ_centeredTruncated_largeDeviation_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a K r x : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K) (hr : 0 ≤ r) (hx : 0 ≤ x)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) (u : E) :
    let G : Omega → E → ℝ := fun omega t ↦
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega t
    mu.real {omega | ∃ t : EuclideanUnitBall E,
      mixedEuclideanProcessBound (2 * (r * K)) (2 * (r * a))
          (finrank ℝ E) x <
        |G omega (u + r • (t : E)) - G omega u|} ≤ Real.exp (-x) := by
  dsimp only
  let G : Omega → E → ℝ := fun omega t ↦
    centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
      (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
      (Finset.range (n + 1)) 0 omega t
  let GLocal : Omega → EuclideanUnitBall E → ℝ := fun omega t ↦
    G omega (u + r • (t : E)) - G omega u
  apply measureReal_unitBall_mixedProcess_largeDeviation_le
    GLocal (by positivity) (by positivity) hx
  · intro omega
    have hG : Continuous (G omega) :=
      continuous_centeredAnchoredTruncatedEmpiricalProcess
        H R (mul_nonneg ha (Real.sqrt_nonneg _)) X hX hHmeas hHcont
          hRmeas hR hLip (Finset.range (n + 1)) 0 omega
    exact (hG.comp
      (continuous_const.add (continuous_const.smul continuous_subtype_val))).sub
        continuous_const
  · intro omega
    simp only [GLocal, G, smul_zero, add_zero, sub_self]
  · intro s t y hy
    have htail :=
      measureReal_range_succ_centeredTruncated_increment_mixedTail
        H R ha hK X hX hIndep hHmeas hRmeas hR hLip hRL2 hRsecond
          n (u + r • (s : E)) (u + r • (t : E)) y hy
    have hdist :
        dist (u + r • (s : E)) (u + r • (t : E)) =
          r * dist s t := by
      rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hr,
        Subtype.dist_eq]
    have hthreshold :
        2 * K * dist (u + r • (s : E)) (u + r • (t : E)) *
              Real.sqrt (2 * y) +
            2 * (2 * a) *
              dist (u + r • (s : E)) (u + r • (t : E)) * y =
          2 * (r * K) * dist s t * Real.sqrt (2 * y) +
            2 * (2 * (r * a)) * dist s t * y := by
      rw [hdist]
      ring
    have hsub : ∀ omega,
        GLocal omega s - GLocal omega t =
          (Real.sqrt (n + 1 : ℝ))⁻¹ *
            ∑ i ∈ Finset.range (n + 1),
              (truncatedLipschitzIncrement H R
                  (a * Real.sqrt (n + 1 : ℝ)) X i
                    (u + r • (s : E)) (u + r • (t : E)) omega -
                ∫ xi, truncatedLipschitzIncrement H R
                  (a * Real.sqrt (n + 1 : ℝ)) X i
                    (u + r • (s : E)) (u + r • (t : E)) xi ∂mu) := by
      intro omega
      calc
        GLocal omega s - GLocal omega t =
            G omega (u + r • (s : E)) - G omega (u + r • (t : E)) := by
              dsimp only [GLocal]
              ring
        _ = _ := centeredAnchoredTruncatedEmpiricalProcess_sub
          H R (mul_nonneg ha (Real.sqrt_nonneg _)) X hX hHmeas hRmeas
            hR hLip (Finset.range (n + 1)) 0 omega
              (u + r • (s : E)) (u + r • (t : E))
    simpa only [hthreshold, hsub] using htail

/-- Local chaining written directly on a closed ball of the ambient
Euclidean space.
@isnad1 id=other.13h13v.s9.b9e4b38940fb from=translated src=- shape=f75de4b9 vocab=38a91ca3
-/
theorem measureReal_closedBall_local_range_succ_centeredTruncated_largeDeviation_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a K r x : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K) (hr : 0 < r) (hx : 0 ≤ x)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) (u : E) :
    let G : Omega → E → ℝ := fun omega t ↦
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega t
    mu.real {omega | ∃ v : E, dist v u ≤ r ∧
      mixedEuclideanProcessBound (2 * (r * K)) (2 * (r * a))
          (finrank ℝ E) x < |G omega v - G omega u|} ≤
      Real.exp (-x) := by
  dsimp only
  let G : Omega → E → ℝ := fun omega t ↦
    centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
      (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
      (Finset.range (n + 1)) 0 omega t
  have hunit :=
    measureReal_unitBall_local_range_succ_centeredTruncated_largeDeviation_le
      H R ha hK hr.le hx X hX hIndep hHmeas hHcont hRmeas hR hLip
        hRL2 hRsecond n u
  apply (measureReal_mono ?_).trans hunit
  intro omega homega
  obtain ⟨v, hv, hbad⟩ := homega
  have hvnorm : ‖v - u‖ ≤ r := by
    simpa only [dist_eq_norm] using hv
  have hinv : 0 ≤ r⁻¹ := (inv_pos.mpr hr).le
  have hqnorm : ‖r⁻¹ • (v - u)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹ * ‖v - u‖ ≤ r⁻¹ * r :=
        mul_le_mul_of_nonneg_left hvnorm hinv
      _ = 1 := inv_mul_cancel₀ hr.ne'
  let q : EuclideanUnitBall E := ⟨r⁻¹ • (v - u), hqnorm⟩
  refine ⟨q, ?_⟩
  have hqpoint : u + r • (q : E) = v := by
    dsimp only [q]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  simpa only [hqpoint] using hbad

/-- A finite volumetric net upgrades the local chaining estimate to a
uniform modulus bound on the Euclidean unit ball.
@isnad1 id=other.13h12v.s9.6f93dbb00769 from=translated src=- shape=a66da71b vocab=13a2be8f
-/
theorem measureReal_unitBall_oscillation_range_succ_centeredTruncated_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a K delta x : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K) (hdelta : 0 < delta) (hx : 0 ≤ x)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) :
    let G : Omega → E → ℝ := fun omega t ↦
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega t
    let L : ℝ := mixedEuclideanProcessBound
      (2 * ((2 * delta) * K)) (2 * ((2 * delta) * a))
        (finrank ℝ E) x
    mu.real {omega | ∃ s t : EuclideanUnitBall E,
      dist s t < delta ∧ 2 * L < |G omega (s : E) - G omega (t : E)|} ≤
        (1 + 2 / delta) ^ finrank ℝ E * Real.exp (-x) := by
  dsimp only
  classical
  let G : Omega → E → ℝ := fun omega t ↦
    centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
      (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
      (Finset.range (n + 1)) 0 omega t
  let L : ℝ := mixedEuclideanProcessBound
    (2 * ((2 * delta) * K)) (2 * ((2 * delta) * a))
      (finrank ℝ E) x
  obtain ⟨N, hnet, hcard⟩ :=
    RandomSetTheory.exists_euclideanUnitBall_finset_net_card_le
      (E := E) hdelta
  let A : EuclideanUnitBall E → Set Omega := fun v ↦
    {omega | ∃ w : E, dist w (v : E) ≤ 2 * delta ∧
      L < |G omega w - G omega (v : E)|}
  have hlocal : ∀ v ∈ N, mu.real (A v) ≤ Real.exp (-x) := by
    intro v hv
    simpa only [A, G, L] using
      (measureReal_closedBall_local_range_succ_centeredTruncated_largeDeviation_le
        H R ha hK (mul_pos (by norm_num) hdelta) hx X hX hIndep
          hHmeas hHcont hRmeas hR hLip hRL2 hRsecond n (v : E))
  have hsubset :
      {omega | ∃ s t : EuclideanUnitBall E,
        dist s t < delta ∧
          2 * L < |G omega (s : E) - G omega (t : E)|} ⊆
        ⋃ v ∈ N, A v := by
    intro omega homega
    obtain ⟨s, t, hst, hbad⟩ := homega
    obtain ⟨v, hvN, hsv⟩ := hnet s
    have hsvE : dist (s : E) (v : E) ≤ delta := by
      simpa only [Subtype.dist_eq] using hsv
    have htvE : dist (t : E) (v : E) ≤ 2 * delta := by
      have htsE : dist (t : E) (s : E) < delta := by
        simpa only [Subtype.dist_eq, dist_comm] using hst
      exact (calc
          dist (t : E) (v : E) ≤
              dist (t : E) (s : E) + dist (s : E) (v : E) :=
            dist_triangle _ _ _
          _ < delta + delta := add_lt_add_of_lt_of_le htsE hsvE
          _ = 2 * delta := by ring).le
    have hsvLocal : dist (s : E) (v : E) ≤ 2 * delta :=
      hsvE.trans (by linarith [hdelta])
    have htriangle :
        |G omega (s : E) - G omega (t : E)| ≤
          |G omega (s : E) - G omega (v : E)| +
            |G omega (t : E) - G omega (v : E)| := by
      calc
        |G omega (s : E) - G omega (t : E)| =
            |(G omega (s : E) - G omega (v : E)) -
              (G omega (t : E) - G omega (v : E))| := by
                congr 1
                ring
        _ ≤ _ := abs_sub _ _
    have hside :
        L < |G omega (s : E) - G omega (v : E)| ∨
          L < |G omega (t : E) - G omega (v : E)| := by
      by_contra h
      push Not at h
      linarith
    apply Set.mem_iUnion.2
    refine ⟨v, Set.mem_iUnion.2 ⟨hvN, ?_⟩⟩
    rcases hside with hs | ht
    · exact ⟨s, hsvLocal, hs⟩
    · exact ⟨t, htvE, ht⟩
  calc
    mu.real {omega | ∃ s t : EuclideanUnitBall E,
        dist s t < delta ∧
          2 * L < |G omega (s : E) - G omega (t : E)|} ≤
        mu.real (⋃ v ∈ N, A v) :=
      measureReal_mono hsubset (measure_ne_top mu _)
    _ ≤ ∑ v ∈ N, mu.real (A v) :=
      measureReal_biUnion_finset_le N A
    _ ≤ ∑ _v ∈ N, Real.exp (-x) := Finset.sum_le_sum hlocal
    _ = N.card * Real.exp (-x) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 + 2 / delta) ^ finrank ℝ E * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le

/-- Dyadic oscillation bound with a summable entropy budget.
@isnad1 id=other.12h12v.s9.bb030742b9fb from=translated src=- shape=fecfbe66 vocab=8a312b7f
-/
theorem measureReal_unitBall_dyadicOscillation_range_succ_centeredTruncated_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a K x : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K) (hx : 0 ≤ x)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n k : ℕ) :
    let d := finrank ℝ E
    let delta := RandomSetTheory.dyadicResolution k
    let confidence := mixedEuclideanConfidence d x k
    let G : Omega → E → ℝ := fun omega t ↦
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega t
    let eta := 2 * mixedEuclideanProcessBound
      (2 * ((2 * delta) * K)) (2 * ((2 * delta) * a)) d confidence
    mu.real {omega | ∃ s t : EuclideanUnitBall E,
      dist s t < delta ∧
        eta < |G omega (s : E) - G omega (t : E)|} ≤
      mixedEuclideanEntropyCost d x k := by
  dsimp only
  let d := finrank ℝ E
  let delta := RandomSetTheory.dyadicResolution k
  let confidence := mixedEuclideanConfidence d x k
  have hosc :=
    measureReal_unitBall_oscillation_range_succ_centeredTruncated_le
      H R ha hK (RandomSetTheory.dyadicResolution_pos k)
        (mixedEuclideanConfidence_nonneg d hx k) X hX hIndep
          hHmeas hHcont hRmeas hR hLip hRL2 hRsecond n
  have hentropy :
      (1 + 2 / delta) ^ d ≤
        Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) := by
    simpa only [d, delta] using
      one_add_two_div_dyadicResolution_pow_le_exp d k
  calc
    mu.real {omega | ∃ s t : EuclideanUnitBall E,
        dist s t < delta ∧
          2 * mixedEuclideanProcessBound
              (2 * ((2 * delta) * K)) (2 * ((2 * delta) * a)) d confidence <
            |centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
                (a * Real.sqrt (n + 1 : ℝ))
                (Real.sqrt (n + 1 : ℝ))⁻¹ X
                (Finset.range (n + 1)) 0 omega (s : E) -
              centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
                (a * Real.sqrt (n + 1 : ℝ))
                (Real.sqrt (n + 1 : ℝ))⁻¹ X
                (Finset.range (n + 1)) 0 omega (t : E)|} ≤
        (1 + 2 / delta) ^ d * Real.exp (-confidence) := by
      simpa only [d, delta, confidence] using hosc
    _ ≤ Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) *
        Real.exp (-confidence) :=
      mul_le_mul_of_nonneg_right hentropy (Real.exp_pos _).le
    _ ≤ Real.exp (4 * (d : ℝ) * (k + 2 : ℝ)) *
        (2 * Real.exp (-confidence)) := by
      gcongr
      linarith [Real.exp_pos (-confidence)]
    _ = mixedEuclideanEntropyCost d x k := by
      rfl

end Euclidean

end ProbabilityTheory
