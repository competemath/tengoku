/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.ComparisonAssembly
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.ComparisonUnimodality

/-!
# Weak logarithmic boundary curvature for the classical pricing contract

The comparison interval invariant is now supplied by the direct three-point
maximum principle. This proves the normalized classical-solution claim, with
no extra expiry, speed, interval, zero-count, or derivative-trace premise.

Identification of this classical contract with the actual continuous-time
American value is separate. Strict logarithmic curvature is not asserted.
The modular stock-curvature consequence below takes strict speed as an argument;
`StrictBoundarySpeed` proves it and `StockConclusion` supplies the final result.

## Result

Public entry points include `dividend_log_curvature`, `dividend_curvature_claim`, `zeroDividend_weak_curvature_claim`, `liuRange_curvature_claim`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Set
open scoped Topology

/--
@isnad1 id=le.2h5v.s6.b72c6cd6cf45 from=translated src=- shape=0e46921b vocab=d275a023
-/
theorem dividend_log_curvature {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) : ∀ t, 0 < t → 0 ≤ deriv (deriv b) t :=
  dividend_curvature_of_comparison_inputs hp
    (fun _ _ hc hd _ ht => straightDifference_positive_interval hp hc hd.le ht)

/--
@isnad1 id=dividend.0h0v.s0.76eaf1d1b838 from=translated src=- shape=45709ebd vocab=76eaf1d1
-/
theorem dividend_curvature_claim : DividendCurvatureClaim := by
  intro k h p b hp
  exact dividend_log_curvature hp

/-- Zero-dividend milestone: weak log curvature on the original contract.
This is the new proof specialized, not an independent CCJZ proof and not the
strict logarithmic curvature statement of that paper.
@isnad1 id=zerodivi.0h0v.s0.85febd8cceea from=translated src=- shape=45709ebd vocab=85febd8c
-/
theorem zeroDividend_weak_curvature_claim : ZeroDividendWeakCurvatureClaim :=
  (dividendCurvature_specializations dividend_curvature_claim).1

/-- Liu-range milestone for the weak logarithmic conclusion of this proof.
@isnad1 id=liurange.0h0v.s0.c7b8a546964a from=translated src=- shape=45709ebd vocab=c7b8a546
-/
theorem liuRange_curvature_claim : LiuRangeCurvatureClaim :=
  (dividendCurvature_specializations dividend_curvature_claim).2

/--
@isnad1 id=lt.5h8v.s7.e37138121515 from=translated src=- shape=3174a08f vocab=a964e554
-/
theorem stock_curvature_of_strict_speed {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (hspeed : ∀ t, 0 < t → deriv b t < 0)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < deriv (deriv (stockBoundary E σ expiry b)) T :=
  stock_curvature_of_comparison_inputs hp hspeed
    (fun _ _ hc hd _ ht => straightDifference_positive_interval hp hc hd.le ht) hE hσ hT

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
