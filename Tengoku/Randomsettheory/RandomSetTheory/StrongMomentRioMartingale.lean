/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentSeriesMartingale
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentRioTransform
import Tengoku.Randomsettheory.RandomSetTheory.MGFChernoffCVaR

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit Rio bounds for strong-moment martingale sums

This file joins the two layers which were previously separate:

* the exact-series conditional MGF and residual estimate for a finite adapted
  martingale-difference sum; and
* the fully optimized deterministic Rio transform.

The resulting CVaR bound has no free Laplace parameter.  Its final term is the
exact price of restoring the upper tails discarded before the martingale MGF
was composed.  Thus the statement is a complete scalar martingale endpoint;
passing from it to Marchina's maximal empirical-process theorem still needs
the product-filtration/finite-supremum identification.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

variable (filtration : Filtration ℕ mOmega)

/-- The scale condition used in Rio's transform also controls the exact
CVaR cost of restoring the discarded upper tails.-/
theorem inv_mul_strongMomentResidual_le_div
    (q : ℕ) (hq : 1 ≤ q) {Q y alpha : ℝ}
    (hy : 0 < y) (halpha0 : 0 < alpha)
    (hscale : Q * Real.exp (-Real.log alpha) ≤ y ^ q) :
    alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) ≤ y / (q : ℝ) := by
  have hscale' : Q * alpha⁻¹ ≤ y ^ q := by
    rw [Real.exp_neg, Real.exp_log halpha0] at hscale
    exact hscale
  have hden : 0 < (q : ℝ) * y ^ (q - 1) := by positivity
  have hquotient :
      (Q * alpha⁻¹) / ((q : ℝ) * y ^ (q - 1)) ≤
        y ^ q / ((q : ℝ) * y ^ (q - 1)) :=
    div_le_div_of_nonneg_right hscale' hden.le
  calc
    alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) =
        (Q * alpha⁻¹) / ((q : ℝ) * y ^ (q - 1)) := by ring
    _ ≤ y ^ q / ((q : ℝ) * y ^ (q - 1)) := hquotient
    _ = y / (q : ℝ) := by
      have hq0 : q ≠ 0 := by omega
      rw [← pow_sub_one_mul hq0 y]
      field_simp [hy.ne']

/-- Fully optimized exact-series strong-moment CVaR estimate for a finite
martingale-difference sum.

`V` and `Q` dominate respectively the aggregate second moment and aggregate
positive `q`-th moment.  The intermediate deterministic proxies are required
to satisfy the sharp Hölder interpolation used in Rio's exponent.-/
theorem conditionalValueAtRisk_sum_le_rioStrongMoment_explicit
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hAdapted : StronglyAdapted filtration D)
    (second : ℕ → ℝ) (moment : ℕ → ℕ → ℝ)
    (n q : ℕ) (hn : 0 < n) (hq : 3 ≤ q)
    {V Q y alpha : ℝ} (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y)
    (hD : ∀ i < n, Integrable (D i) mu)
    (hDsq : ∀ i < n, Integrable (fun omega ↦ D i omega ^ 2) mu)
    (hpow : ∀ i < n, ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦ (max (D i omega) 0) ^ k) mu)
    (hcenter0 : ∫ omega, D 0 omega ∂mu = 0)
    (hcenterSucc : ∀ i < n - 1,
      mu[D (i + 1) | filtration i] =ᵐ[mu] 0)
    (hsecond0 : (∫ omega, D 0 omega ^ 2 ∂mu) ≤ second 0)
    (hsecondSucc : ∀ i < n - 1,
      mu[fun omega ↦ D (i + 1) omega ^ 2 | filtration i] ≤ᵐ[mu]
        fun _ ↦ second (i + 1))
    (hmoment0 : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D 0 omega) 0) ^ k ∂mu) ≤ moment 0 k)
    (hmomentSucc : ∀ i < n - 1, ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega ↦ (max (D (i + 1) omega) 0) ^ k | filtration i]
        ≤ᵐ[mu] fun _ ↦ moment (i + 1) k)
    (hsecond : (∑ i ∈ Finset.range n, second i) ≤ V)
    (hmiddle : ∀ k ∈ Finset.Ico 3 q,
      (∑ i ∈ Finset.range n, moment i k) ≤
        interpolatedStrongMomentCoefficient q V Q k)
    (hmomentQ : (∑ i ∈ Finset.range n, moment i q) ≤ Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) ≤ y ^ q) :
    conditionalValueAtRisk alpha
        (fun omega ↦ ∑ i ∈ Finset.range n, D i omega) mu ≤
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
        alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) := by
  let U : Omega → ℝ := fun omega ↦
    ∑ i ∈ Finset.range n, upperTruncation (D i) y omega
  let R : Omega → ℝ := fun omega ↦
    ∑ i ∈ Finset.range n, upperTruncationResidual (D i) y omega
  let seriesExponent : ℝ → ℝ := fun t ↦
    strongMomentSeriesExponent q t y
      (∑ i ∈ Finset.range n, second i)
      (fun k ↦ ∑ i ∈ Finset.range n, moment i k)
  have hUInt : Integrable U mu := by
    dsimp only [U]
    apply integrable_finsetSum
    intro i hi
    exact integrable_upperTruncation (hD i (Finset.mem_range.mp hi)) y
  have hRInt : Integrable R mu := by
    dsimp only [R]
    apply integrable_finsetSum
    intro i hi
    exact integrable_upperTruncationResidual
      (hD i (Finset.mem_range.mp hi)) y
  have hmgfSeries : HasOneSidedMGF U seriesExponent mu := by
    simpa only [U, seriesExponent] using
      hasOneSidedMGF_sum_upperTruncation_of_strongMomentSeries
        filtration D hAdapted second moment n q hn hq hy hD hDsq hpow
          hcenter0 hcenterSucc hsecond0 hsecondSucc hmoment0 hmomentSucc
  have hseriesLe : ∀ t : ℝ, 0 ≤ t →
      seriesExponent t ≤ rioStrongMomentExponent q V Q y t := by
    intro t ht
    exact strongMomentSeriesExponent_le_rioStrongMomentExponent
      q ht hy hsecond hmiddle hmomentQ
  have hmgfRio : HasOneSidedMGF U (rioStrongMomentExponent q V Q y) mu :=
    hmgfSeries.mono_exponent hseriesLe
  have hx : 0 < -Real.log alpha :=
    neg_pos.mpr (Real.log_neg halpha0 halpha1)
  have hcvarU : conditionalValueAtRisk alpha U mu ≤
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 := by
    have hchernoff := hmgfRio.conditionalValueAtRisk_le_chernoffTransform
      hUInt halpha0 halpha1.le
    exact hchernoff.trans
      (chernoffTransform_rioStrongMomentExponent_le_explicit
        q hq hV hQ hy hx hscale)
  have hqIcc : q ∈ Finset.Icc 2 q :=
    Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hpowq : ∀ i < n,
      Integrable (fun omega ↦ (max (D i omega) 0) ^ q) mu := by
    intro i hi
    exact hpow i hi q hqIcc
  have hmomentQEach : ∀ i < n,
      (∫ omega, (max (D i omega) 0) ^ q ∂mu) ≤ moment i q := by
    intro i hi
    cases i with
    | zero => exact hmoment0 q hqIcc
    | succ i =>
        have hiPred : i < n - 1 := by omega
        have hcond := hmomentSucc i hiPred q hqIcc
        have hint :
            (∫ omega,
                mu[fun z ↦ (max (D (i + 1) z) 0) ^ q |
                  filtration i] omega ∂mu) ≤
              ∫ _ : Omega, moment (i + 1) q ∂mu :=
          integral_mono_ae integrable_condExp (integrable_const _) hcond
        rw [integral_condExp (filtration.le i), integral_const] at hint
        simpa only [probReal_univ, smul_eq_mul, one_mul] using hint
  have hrawMoment :
      (∑ i ∈ Finset.range n,
        ∫ omega, (max (D i omega) 0) ^ q ∂mu) ≤ Q := by
    exact (Finset.sum_le_sum fun i hi ↦
      hmomentQEach i (Finset.mem_range.mp hi)).trans hmomentQ
  have hresidualBase :=
    conditionalValueAtRisk_sum_upperTruncationResidual_le
      D n q (by omega) hD hpowq hy halpha0 halpha1.le
  have hden : 0 < (q : ℝ) * y ^ (q - 1) := by positivity
  have hresidual : conditionalValueAtRisk alpha R mu ≤
      alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) := by
    have hresidualBase' : conditionalValueAtRisk alpha R mu ≤
        alpha⁻¹ *
          ((∑ i ∈ Finset.range n,
            ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
              ((q : ℝ) * y ^ (q - 1))) := by
      simpa only [R] using hresidualBase
    have hproxy :
        alpha⁻¹ *
            ((∑ i ∈ Finset.range n,
              ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
                ((q : ℝ) * y ^ (q - 1))) ≤
          alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hrawMoment hden.le)
        (inv_nonneg.mpr halpha0.le)
    exact hresidualBase'.trans hproxy
  have hdecomp :
      (fun omega ↦ ∑ i ∈ Finset.range n, D i omega) =
        fun omega ↦ U omega + R omega := by
    funext omega
    dsimp only [U, R]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (upperTruncation_add_residual (D i) y omega).symm
  rw [hdecomp]
  exact (conditionalValueAtRisk_add_le hUInt hRInt
    halpha0 halpha1.le).trans (add_le_add hcvarU hresidual)

end ProbabilityTheory
