/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentRioConfidence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial-rate form of Rio's confidence radius

The exact confidence radius contains a term proportional to
`Q^(1/q) * log (1 / alpha)`.  The elementary inequality

`log x <= q * x^(1/q)`

absorbs this term into the polynomial confidence scale.  The resulting
coefficient is explicit and depends on `q`; this dependence must not be
hidden behind a universal constant independent of the moment order.
-/

open Real
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The natural empirical order-`q` scale after summing `n` normalized
coordinates whose raw `q`-th moments are bounded by `K^q`.-/
def empiricalPolynomialScale (q n : Nat) (K : Real) : Real :=
  2 * K / (n : Real) ^ (1 - 1 / (q : Real))

/-- Exact simplification of the strong-moment root at the empirical moment
value produced by `EmpiricalEnvelopeMomentScaling`.
@isnad1 id=eq.3h3v.s6.1d3a133c9d01 from=translated src=- shape=a1f776cf vocab=09f07062
-/
theorem strongMomentQScale_empiricalMoment
    {q n : Nat} (hq : 1 <= q) (hn : 0 < n) {K : Real} (hK : 0 < K) :
    strongMomentQScale q
        ((2 : Real) ^ q * K ^ q / (n : Real) ^ (q - 1)) =
      empiricalPolynomialScale q n K := by
  have hq0 : q ≠ 0 := by omega
  have hqReal : (q : Real) ≠ 0 := by exact_mod_cast hq0
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have htwoK : 0 <= 2 * K := (mul_pos (by norm_num) hK).le
  have hden : 0 <= (n : Real) ^ (q - 1) := pow_nonneg hnReal.le _
  have hexponent :
      ((q - 1 : Nat) : Real) * (q : Real)⁻¹ =
        1 - (q : Real)⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 <= q)]
    norm_num
    field_simp [hqReal]
  unfold strongMomentQScale empiricalPolynomialScale
  rw [show (2 : Real) ^ q * K ^ q = (2 * K) ^ q by rw [mul_pow]]
  rw [Real.div_rpow (pow_nonneg htwoK q) hden]
  simp only [one_div]
  rw [Real.pow_rpow_inv_natCast htwoK hq0]
  rw [← Real.rpow_natCast_mul hnReal.le (q - 1) (q : Real)⁻¹]
  rw [hexponent]

/-- The same simplification after adding the confidence power
`alpha^(-1/q)`.
@isnad1 id=eq.3h4v.s7.9e4b3b64fc8a from=translated src=- shape=405c6229 vocab=920dd872
-/
theorem rioConfidenceScale_empiricalMoment
    {q n : Nat} (hq : 1 <= q) (hn : 0 < n) {K alpha : Real}
    (hK : 0 < K) :
    rioConfidenceScale q
        ((2 : Real) ^ q * K ^ q / (n : Real) ^ (q - 1)) alpha =
      empiricalPolynomialScale q n K *
        (1 / alpha) ^ (1 / (q : Real)) := by
  unfold rioConfidenceScale
  rw [strongMomentQScale_empiricalMoment hq hn hK]

/-- Explicit coefficient obtained when the logarithmic Rio term is absorbed
into the order-`q` confidence scale.-/
def rioPolynomialCoefficient (q : Nat) : Real :=
  1 + 2 / (q : Real) + Real.exp 1 * (q : Real) / 3

/-- The logarithmic confidence factor is bounded by the polynomial factor
`q * alpha^(-1/q)`.
@isnad1 id=le.2h2v.s6.232b0ba3ac1a from=translated src=- shape=95d7db40 vocab=cf21e088
-/
theorem neg_log_le_natCast_mul_inv_rpow
    {q : Nat} (hq : 1 <= q) {alpha : Real}
    (halpha0 : 0 < alpha) :
    -Real.log alpha <=
      (q : Real) * (1 / alpha) ^ (1 / (q : Real)) := by
  have hqReal : 0 < (q : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hepsilon : 0 < 1 / (q : Real) := one_div_pos.mpr hqReal
  have hlog := Real.log_le_rpow_div
    (show 0 <= 1 / alpha from (one_div_pos.mpr halpha0).le) hepsilon
  have hlog' :
      -Real.log alpha <=
        (1 / alpha) ^ (1 / (q : Real)) / (1 / (q : Real)) := by
    simpa only [one_div, Real.log_inv] using hlog
  calc
    -Real.log alpha <=
        (1 / alpha) ^ (1 / (q : Real)) / (1 / (q : Real)) := hlog'
    _ = (q : Real) * (1 / alpha) ^ (1 / (q : Real)) := by
      field_simp [hqReal.ne']

/-- Report-shaped polynomial upper bound for the exact Rio confidence
radius.  The Gaussian part is unchanged; all strong-moment contributions
are collected into one explicit order-`q` coefficient.
@isnad1 id=le.3h4v.s6.98d9048cc1d4 from=translated src=- shape=95ce4740 vocab=784b527c
-/
theorem rioStrongMomentConfidenceRadius_le_polynomialRate
    {q : Nat} (hq : 1 <= q) {V Q alpha : Real}
    (hQ : 0 < Q) (halpha0 : 0 < alpha) :
    rioStrongMomentConfidenceRadius q V Q alpha <=
      Real.sqrt (2 * V * (-Real.log alpha)) +
        rioPolynomialCoefficient q * rioConfidenceScale q Q alpha := by
  have hscalePos : 0 < strongMomentQScale q Q :=
    strongMomentQScale_pos hQ
  have hpowerPos : 0 < (1 / alpha) ^ (1 / (q : Real)) :=
    Real.rpow_pos_of_pos (one_div_pos.mpr halpha0) _
  have hlog := neg_log_le_natCast_mul_inv_rpow hq halpha0
  have hlogTerm :
      Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 <=
        (Real.exp 1 * (q : Real) / 3) *
          rioConfidenceScale q Q alpha := by
    unfold rioConfidenceScale
    have hmul := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (Real.exp_pos 1).le hscalePos.le)
    nlinarith
  unfold rioStrongMomentConfidenceRadius rioPolynomialCoefficient
  linarith

/-- Fully explicit empirical specialization of the polynomial-rate bound.
The order-two term is kept under its exact square root, while the order-`q`
term is displayed at scale `Kq / n^(1-1/q) * alpha^(-1/q)`.
@isnad1 id=le.4h5v.s8.c15a96eab38d from=translated src=- shape=abb42f57 vocab=8ad4dfe8
-/
theorem rioStrongMomentConfidenceRadius_empiricalMoment_le
    {q n : Nat} (hq : 1 <= q) (hn : 0 < n)
    {Ktwo Kq alpha : Real} (hKq : 0 < Kq) (halpha0 : 0 < alpha) :
    rioStrongMomentConfidenceRadius q
        (4 * Ktwo ^ 2 / (n : Real))
        ((2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1)) alpha <=
      Real.sqrt
          (2 * (4 * Ktwo ^ 2 / (n : Real)) * (-Real.log alpha)) +
        rioPolynomialCoefficient q * empiricalPolynomialScale q n Kq *
          (1 / alpha) ^ (1 / (q : Real)) := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hQ : 0 < (2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1) := by
    exact div_pos
      (mul_pos (pow_pos (by norm_num) q) (pow_pos hKq q))
      (pow_pos hnReal (q - 1))
  have hbound := rioStrongMomentConfidenceRadius_le_polynomialRate
    (V := 4 * Ktwo ^ 2 / (n : Real)) hq hQ halpha0
  rw [rioConfidenceScale_empiricalMoment hq hn hKq] at hbound
  simpa only [mul_assoc] using hbound

end ProbabilityTheory
