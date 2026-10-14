/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku.FormalMathfin.MathFin.Actuarial.Mortality
public import Tengoku.FormalMathfin.MathFin.FixedIncome.HazardCurve

/-!
# Bridge: actuarial survival ≡ reduced-form credit survival

The actuarial survival function built from a force of mortality `μ` and the
reduced-form credit survival function built from a hazard rate `h` are the *same*
object — both are defined as `survivalFromIntensity = exp(-∫₀ᵗ ·)`. Mortality,
credit hazard, and exponential discounting are three faces of one
`ExponentialDiscount` calculus (cf. Jarrow–Turnbull 1995). A certified unification
of two known textbook facts — **not** new finance.

This is one of the library's two illustrative *certified cross-domain bridges*
(the other being `Bridges/ConcentrationVariance.lean`): a machine-checked identity
showing that two independently-developed modules denote the same mathematics.
-/

@[expose] public section

namespace MathFin

/-- **Survival unification.** The actuarial `survivalFromForce` and the credit
`hazardSurvival` are *definitionally* the same function — both unfold to
`survivalFromIntensity` — so for every intensity `μ` and time `t` they agree.
@isnad1 id=eq.0h2v.s3.5102fc10bb91 from=translated src=- shape=3517c150 vocab=66a021a5
-/
theorem survivalFromForce_eq_hazardSurvival (μ : ℝ → ℝ) (t : ℝ) :
    survivalFromForce μ t = hazardSurvival μ t := rfl

/-- **Gompertz law as a credit hazard curve.** A Gompertz-shaped intensity
`h(u) = B · e^{c u}` has cumulative hazard `(B/c) · (e^{c t} − 1)` — the actuarial
Gompertz cumulative force, reused as a reduced-form credit term structure.
@isnad1 id=eq.1h3v.s6.2b395e69b0fa from=translated src=- shape=c24771e9 vocab=eb21f393
-/
theorem gompertz_cumHazard (B c t : ℝ) (hc : c ≠ 0) :
    cumHazard (fun u ↦ B * Real.exp (c * u)) t = (B / c) * (Real.exp (c * t) - 1) := by
  unfold cumHazard
  exact gompertz_cumulative_force B c t hc

end MathFin
