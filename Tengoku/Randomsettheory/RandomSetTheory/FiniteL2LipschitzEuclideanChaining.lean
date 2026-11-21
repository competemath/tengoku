/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.L2LipschitzEuclideanChaining

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-sample L2 Lipschitz chaining

This module gives the finite-index counterpart of the prefix-process theorem
in `L2LipschitzEuclideanChaining`.  It is useful for heavy-tail truncation at
an arbitrary deterministic level `M`: the Gaussian metric remembers the
second moment `K`, while the Bernstein metric remembers only `M`.

For an average of `N` observations (`c = 1 / N`) the two scales are

* `sqrt (2 * N) * c * K`, of order `K / sqrt N`;
* `2 * c * M`, of order `M / N`.

Thus hard truncation followed by this theorem yields the usual Gaussian term
and an explicit dimension-dependent Bernstein remainder without invoking a
maximal Fuk--Nagaev theorem.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology
open RandomSetTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega Z iota E : Type*} [MeasurableSpace Omega] [MeasurableSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {mu : Measure Omega}

/-- Variance-sensitive metric scale of a finite centered truncated sum.-/
def finiteTruncatedGaussianScale (I : Finset iota) (c : ℝ≥0) (K : ℝ) : ℝ :=
  Real.sqrt (2 * (I.card : ℝ)) * (c : ℝ) * K

/-- Bernstein metric scale of a finite centered truncated sum.-/
def finiteTruncatedLinearScale (c : ℝ≥0) (M : ℝ) : ℝ :=
  2 * (c : ℝ) * M

/--
@isnad1 id=le.1h4v.s5.da6232a03752 from=translated src=- shape=4a3591ab vocab=965591f1
-/
theorem finiteTruncatedGaussianScale_nonneg
    (I : Finset iota) (c : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ finiteTruncatedGaussianScale I c K := by
  unfold finiteTruncatedGaussianScale
  positivity

/--
@isnad1 id=le.1h2v.s4.b0cc3b4817ca from=translated src=- shape=696abc3b vocab=d33648e0
-/
theorem finiteTruncatedLinearScale_nonneg
    (c : ℝ≥0) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ finiteTruncatedLinearScale c M := by
  unfold finiteTruncatedLinearScale
  positivity

/-- Uniform Bernstein chaining for a finite centered truncated process on a
Euclidean unit ball.  Unlike the prefix theorem, this statement accepts an
arbitrary finite index type and arbitrary normalization `c`.
@isnad1 id=other.14h13v.s9.4f86c6eb8199 from=translated src=- shape=1db43808 vocab=e5090ba4
-/
theorem measureReal_unitBall_finite_centeredTruncated_largeDeviation_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {M K x : ℝ}
    (hM : 0 ≤ M) (hK : 0 < K) (hx : 0 ≤ x)
    (c : ℝ≥0) (hc : 0 < c)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (I : Finset iota) (hI : I.Nonempty)
    (hRL2 : ∀ i ∈ I, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i ∈ I, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2) :
    let G : Omega → EuclideanUnitBall E → ℝ := fun omega t ↦
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R M (c : ℝ)
        X I 0 omega (t : E)
    mu.real {omega | ∃ t : EuclideanUnitBall E,
      mixedEuclideanProcessBound
          (finiteTruncatedGaussianScale I c K)
          (finiteTruncatedLinearScale c M) (finrank ℝ E) x <
        |G omega t|} ≤ Real.exp (-x) := by
  dsimp only
  let sigma2 : ℝ := finiteTruncatedGaussianScale I c K
  let sigma1 : ℝ := finiteTruncatedLinearScale c M
  let G : Omega → EuclideanUnitBall E → ℝ := fun omega t ↦
    centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R M (c : ℝ)
      X I 0 omega (t : E)
  apply measureReal_unitBall_mixedProcess_largeDeviation_le
    G (finiteTruncatedGaussianScale_nonneg I c hK.le)
      (finiteTruncatedLinearScale_nonneg c hM) hx
  · intro omega
    exact (continuous_centeredAnchoredTruncatedEmpiricalProcess
      H R hM X hX hHmeas hHcont hRmeas hR hLip I 0 omega).comp
        continuous_subtype_val
  · intro omega
    exact centeredAnchoredTruncatedEmpiricalProcess_anchor
      H R M (c : ℝ) X I 0 omega
  · intro s t y hy
    by_cases hst : s = t
    · subst t
      simp only [dist_self, mul_zero, zero_mul, add_zero, sub_self, abs_zero,
        lt_self_iff_false, Set.ofPred_false, measureReal_empty]
      positivity
    · have hdist : 0 < dist s t := dist_pos.mpr hst
      let v : ℝ≥0 := c ^ 2 *
        ∑ _i ∈ I, nnrealOfNonneg (2 * (K * dist s t) ^ 2) (by positivity)
      let b : ℝ≥0 := c *
        nnrealOfNonneg (2 * (M * dist s t)) (by positivity)
      have hmgf : HasBernsteinMGF
          (fun omega ↦ (c : ℝ) * ∑ i ∈ I,
            (truncatedLipschitzIncrement H R M X i (s : E) (t : E) omega -
              ∫ xi, truncatedLipschitzIncrement H R M X i
                (s : E) (t : E) xi ∂mu)) v b mu := by
        simpa only [v, b, Subtype.dist_eq] using
          (hasBernsteinMGF_centeredTruncatedEmpiricalProcess_increment
            (μ := mu) H R c hM hK.le X hX hIndep hHmeas hRmeas hR hLip I
              hRL2 hRsecond (s : E) (t : E))
      have hvpos : 0 < (v : ℝ) := by
        dsimp only [v]
        push_cast
        simp only [coe_nnrealOfNonneg, Finset.sum_const, nsmul_eq_mul]
        have hcard : 0 < (I.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hI
        positivity
      have htail := hmgf.measureReal_abs_gt_mixedThreshold_le hy hvpos
      have hv : (v : ℝ) = (sigma2 * dist s t) ^ 2 := by
        dsimp only [v, sigma2, finiteTruncatedGaussianScale]
        push_cast
        simp only [coe_nnrealOfNonneg, Finset.sum_const, nsmul_eq_mul]
        have hsqrtcard :
            (Real.sqrt (2 * (I.card : ℝ))) ^ 2 = 2 * (I.card : ℝ) := by
          rw [Real.sq_sqrt]
          positivity
        calc
          (c : ℝ) ^ 2 * ((I.card : ℝ) *
              (2 * (K * dist s t) ^ 2)) =
              (2 * (I.card : ℝ)) * (c : ℝ) ^ 2 * K ^ 2 *
                dist s t ^ 2 := by ring
          _ = (Real.sqrt (2 * (I.card : ℝ))) ^ 2 * (c : ℝ) ^ 2 *
                K ^ 2 * dist s t ^ 2 := by rw [hsqrtcard]
          _ = (Real.sqrt (2 * (I.card : ℝ)) * (c : ℝ) * K *
                dist s t) ^ 2 := by ring
      have hb : (b : ℝ) = sigma1 * dist s t := by
        dsimp only [b, sigma1, finiteTruncatedLinearScale]
        push_cast
        simp only [coe_nnrealOfNonneg]
        ring
      have hsigmaDist : 0 ≤ sigma2 * dist s t := by
        dsimp only [sigma2]
        exact mul_nonneg (finiteTruncatedGaussianScale_nonneg I c hK.le)
          dist_nonneg
      have hsqrt :
          Real.sqrt (2 * (v : ℝ) * y) =
            sigma2 * dist s t * Real.sqrt (2 * y) := by
        have hleft : 0 ≤ Real.sqrt (2 * (v : ℝ) * y) :=
          Real.sqrt_nonneg _
        have hright :
            0 ≤ sigma2 * dist s t * Real.sqrt (2 * y) :=
          mul_nonneg hsigmaDist (Real.sqrt_nonneg _)
        have hleftsq :
            (Real.sqrt (2 * (v : ℝ) * y)) ^ 2 =
              2 * (v : ℝ) * y := by
          rw [Real.sq_sqrt]
          positivity
        have hrightsq :
            (sigma2 * dist s t * Real.sqrt (2 * y)) ^ 2 =
              2 * (v : ℝ) * y := by
          rw [mul_pow, Real.sq_sqrt]
          · rw [hv]
            ring
          · positivity
        nlinarith
      have hthreshold :
          bernsteinMixedThreshold (v : ℝ) (b : ℝ) y =
            sigma2 * dist s t * Real.sqrt (2 * y) +
              2 * sigma1 * dist s t * y := by
        unfold bernsteinMixedThreshold
        rw [hsqrt, hb]
        ring
      have hsub : ∀ omega, G omega s - G omega t =
          (c : ℝ) * ∑ i ∈ I,
            (truncatedLipschitzIncrement H R M X i (s : E) (t : E) omega -
              ∫ xi, truncatedLipschitzIncrement H R M X i
                (s : E) (t : E) xi ∂mu) := by
        intro omega
        exact centeredAnchoredTruncatedEmpiricalProcess_sub
          H R hM X hX hHmeas hRmeas hR hLip I 0 omega (s : E) (t : E)
      simpa only [G, hsub, hthreshold, Subtype.dist_eq, sigma2, sigma1]
        using htail

end ProbabilityTheory
