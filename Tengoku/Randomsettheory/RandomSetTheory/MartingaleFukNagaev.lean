/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.CVaRQuantile
import Tengoku.Randomsettheory.RandomSetTheory.MartingaleVarianceBernstein
import Tengoku.Randomsettheory.RandomSetTheory.WeakMoment
import Tengoku.Seed.Probability.CondVar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A variance-sensitive martingale Fuk--Nagaev truncation step

Marchina's Theorem 5.5 is an integrated-quantile (equivalently CVaR) form of
Rio's martingale Fuk--Nagaev inequality.  Its sharp Gaussian term is not a
formal consequence of the elementary Bernstein--Freedman estimate: directly
inverting that estimate introduces a term linear in the truncation level and
in `log (1 / u)`.

This file proves a substantial part of the missing argument without assuming
a concentration certificate:

* centring a hard truncation contracts its (conditional) second moment;
* consequently the truncated martingale keeps the original deterministic
  conditional-variance proxy;
* a deterministic split of Bernstein--Freedman gives a genuine
  Gaussian-plus-polynomial bound, with no logarithmic linear term;
* the result is combined with the martingale truncation decomposition and
  conditional moment control of its predictable bias.

The polynomial term obtained here is the price of replacing the large-scale
part of Bernstein's exponential by a power bound.  It is not yet Marchina's
sharp weak-tail CVaR term.  Reaching that exact statement still requires the
Rio--Pinelis convex-order/integrated-quantile comparison for bounded-above
martingale differences; no such comparison is currently available in the
imported Mathlib API.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

/-! ## Second-moment contraction under centred truncation -/

/-- Ordinary centring after hard truncation does not increase the second
moment.  This is the variance identity followed by the pointwise contraction
`|truncation X y| <= |X|`.-/
theorem integral_sq_centeredTruncation_le_integral_sq
    [IsProbabilityMeasure mu] {X : Omega → ℝ} (hX : MemLp X 2 mu)
    (y : ℝ) :
    ∫ omega, centeredTruncation X y mu omega ^ 2 ∂mu ≤
      ∫ omega, X omega ^ 2 ∂mu := by
  let W : Omega → ℝ := truncation X y
  have hW : MemLp W 2 mu :=
    hX.aestronglyMeasurable.memLp_truncation
  have hcentered :
      ∫ omega, centeredTruncation X y mu omega ^ 2 ∂mu =
        Var[W; mu] := by
    simpa only [centeredTruncation, W] using
      (variance_eq_integral hW.aemeasurable).symm
  have htruncSq : ∀ omega, W omega ^ 2 ≤ X omega ^ 2 := by
    intro omega
    rw [sq_le_sq]
    exact abs_truncation_le_abs_self X y omega
  calc
    ∫ omega, centeredTruncation X y mu omega ^ 2 ∂mu =
        Var[W; mu] := hcentered
    _ = (∫ omega, W omega ^ 2 ∂mu) -
        (∫ omega, W omega ∂mu) ^ 2 := variance_eq_sub hW
    _ ≤ ∫ omega, W omega ^ 2 ∂mu := by
      nlinarith [sq_nonneg (∫ omega, W omega ∂mu)]
    _ ≤ ∫ omega, X omega ^ 2 ∂mu :=
      integral_mono hW.integrable_sq hX.integrable_sq htruncSq

/-- Conditional centring after hard truncation does not increase the
conditional second moment.  The left-hand side is the conditional variance
of the truncation; `condVar_ae_le_condExp_sq` and conditional monotonicity
then compare it to the raw square.-/
theorem condExp_sq_conditionallyCenteredTruncation_le_condExp_sq
    [IsProbabilityMeasure mu] (hm : m ≤ mOmega)
    {X : Omega → ℝ} (hX : MemLp X 2 mu) (y : ℝ) :
    mu[fun omega ↦
        conditionallyCenteredTruncation mu m X y omega ^ 2 | m]
      ≤ᵐ[mu] mu[fun omega ↦ X omega ^ 2 | m] := by
  let W : Omega → ℝ := truncation X y
  have hW : MemLp W 2 mu :=
    hX.aestronglyMeasurable.memLp_truncation
  have hvariance :
      mu[fun omega ↦
          conditionallyCenteredTruncation mu m X y omega ^ 2 | m]
        ≤ᵐ[mu] mu[fun omega ↦ W omega ^ 2 | m] := by
    change mu[(W - mu[W | m]) ^ 2 | m] ≤ᵐ[mu] mu[W ^ 2 | m]
    exact condVar_ae_le_condExp_sq (X := W) hm hW
  have htruncSq : ∀ᵐ omega ∂mu, W omega ^ 2 ≤ X omega ^ 2 := by
    filter_upwards [] with omega
    rw [sq_le_sq]
    exact abs_truncation_le_abs_self X y omega
  exact hvariance.trans
    (condExp_mono (m := m) hW.integrable_sq hX.integrable_sq htruncSq)

/-! ## Turning Bernstein's large-scale regime into a power tail -/

/-- The elementary comparison `exp (-z) <= r! / z^r`.  Keeping the
factorial gives a clean exact constant and avoids any asymptotic estimate for
`r!`.-/
theorem exp_neg_le_factorial_div_pow (r : ℕ) {z : ℝ} (hz : 0 < z) :
    exp (-z) ≤ (r.factorial : ℝ) / z ^ r := by
  have hseries : z ^ r / (r.factorial : ℝ) ≤ exp z :=
    Real.pow_div_factorial_le_exp z hz.le r
  have hden : 0 < z ^ r / (r.factorial : ℝ) := by positivity
  calc
    exp (-z) = 1 / exp z := by rw [Real.exp_neg]; simp only [one_div]
    _ ≤ 1 / (z ^ r / (r.factorial : ℝ)) :=
      one_div_le_one_div_of_le hden hseries
    _ = (r.factorial : ℝ) / z ^ r := by
      field_simp

/-- Deterministic Gaussian/polynomial split of the Bernstein exponent.

For `b*x <= 2*V` the Bernstein denominator is at most `8*V`, giving the
Gaussian term.  In the complementary regime it gives `exp (-x/(4*b))`,
which is bounded by the displayed power term.-/
theorem exp_neg_sq_div_bernstein_le_gaussian_add_polynomial
    (r : ℕ) {x V b : ℝ} (hx : 0 < x) (hV : 0 < V) (hb : 0 < b) :
    exp (-x ^ 2 / (2 * (2 * V + b * x))) ≤
      exp (-x ^ 2 / (8 * V)) +
        (r.factorial : ℝ) * (4 * b / x) ^ r := by
  by_cases hsmall : b * x ≤ 2 * V
  · have hden : 0 < 2 * (2 * V + b * x) := by positivity
    have hdenLe : 2 * (2 * V + b * x) ≤ 8 * V := by nlinarith
    have hfrac : x ^ 2 / (8 * V) ≤
        x ^ 2 / (2 * (2 * V + b * x)) :=
      div_le_div_of_nonneg_left (sq_nonneg x) hden hdenLe
    have hexp : exp (-x ^ 2 / (2 * (2 * V + b * x))) ≤
        exp (-x ^ 2 / (8 * V)) := by
      apply exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hfrac
    exact hexp.trans (le_add_of_nonneg_right (by positivity))
  · have hlarge : 2 * V < b * x := lt_of_not_ge hsmall
    have hden : 0 < 2 * (2 * V + b * x) := by positivity
    have hfour : 0 < 4 * b * x := by positivity
    have hdenLt : 2 * (2 * V + b * x) < 4 * b * x := by nlinarith
    have hfrac : x / (4 * b) ≤
        x ^ 2 / (2 * (2 * V + b * x)) := by
      have hraw : x ^ 2 / (4 * b * x) ≤
          x ^ 2 / (2 * (2 * V + b * x)) :=
        div_le_div_of_nonneg_left (sq_nonneg x) hden hdenLt.le
      convert hraw using 1
      field_simp
    have hexp : exp (-x ^ 2 / (2 * (2 * V + b * x))) ≤
        exp (-(x / (4 * b))) := by
      apply exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hfrac
    have hpower := exp_neg_le_factorial_div_pow r
      (div_pos hx (by positivity : 0 < 4 * b))
    have hrewrite :
        (r.factorial : ℝ) / (x / (4 * b)) ^ r =
          (r.factorial : ℝ) * (4 * b / x) ^ r := by
      rw [div_eq_mul_inv, ← inv_pow]
      congr 2
      field_simp
    calc
      exp (-x ^ 2 / (2 * (2 * V + b * x))) ≤
          exp (-(x / (4 * b))) := hexp
      _ ≤ (r.factorial : ℝ) / (x / (4 * b)) ^ r := hpower
      _ = (r.factorial : ℝ) * (4 * b / x) ^ r := hrewrite
      _ ≤ exp (-x ^ 2 / (8 * V)) +
          (r.factorial : ℝ) * (4 * b / x) ^ r :=
        le_add_of_nonneg_left (exp_pos _).le

/-! ## Variance-sensitive concentration for centred martingale truncations -/

variable (filtration : Filtration ℕ mOmega)

/-! ## Fuk--Nagaev decomposition with the variance-sensitive term -/

end ProbabilityTheory
