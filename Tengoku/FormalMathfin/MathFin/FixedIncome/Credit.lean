/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

/-!
# Reduced-form credit risk under constant hazard rate

The simplest credit-risk model assumes a constant hazard (default-intensity)
rate `h ≥ 0`. The survival probability between `t` and `T` is

  `S(t, T) = exp(-(h · (T - t)))`,

and the resulting credit spread (additional yield over the risk-free rate)
equals the hazard rate itself:

  `c(t, T) = -log(S(t, T)) / (T - t) = h`.

This is structurally identical to the ZCB-yield identity in `ZCB.lean`
(`zcb_yield_eq_rate`), with the hazard `h` playing the role of the risk-free
rate. The continuous-time stochastic-intensity model (Cox process / doubly
stochastic Poisson) is gated on the Itô integral and is not formalized here.

Results:

* `survivalProbability`: definition.
* `survival_at_zero`: `S(T, T) = 1`.
* `survival_pos`: survival probability is positive.
* `creditSpread_eq_hazard`: under constant hazard, spread equals hazard.
* `survival_strictAnti_of_pos_hazard`: positive hazard → strictly decreasing
  survival in horizon `T`.
-/

@[expose] public section

namespace MathFin

open Real

/-- Survival probability under a constant hazard rate `h`. -/
noncomputable def survivalProbability (h t T : ℝ) : ℝ :=
  Real.exp (-(h * (T - t)))

/-- At `T = t`, survival is 1 (no time elapsed).
@isnad1 id=eq.0h2v.s4.e57c1bbd5e37 from=translated src=- shape=c2a510d9 vocab=a914e3e5
-/
lemma survival_at_zero (h T : ℝ) : survivalProbability h T T = 1 := by
  unfold survivalProbability
  rw [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- Survival probability is strictly positive.
@isnad1 id=lt.0h3v.s4.fb8414aab311 from=translated src=- shape=ac9c39a3 vocab=00ab2f4e
-/
lemma survival_pos (h t T : ℝ) : 0 < survivalProbability h t T := Real.exp_pos _

/-- **Credit spread equals hazard rate** under constant hazard:
`-log(S(t, T)) / (T − t) = h`.
@isnad1 id=eq.1h3v.s5.af195e96703f from=translated src=- shape=6e13cf87 vocab=7eeac34e
-/
lemma creditSpread_eq_hazard {h t T : ℝ} (htT : t < T) :
    -Real.log (survivalProbability h t T) / (T - t) = h := by
  unfold survivalProbability
  rw [Real.log_exp, neg_neg]
  have h_ne : T - t ≠ 0 := sub_ne_zero.mpr htT.ne'
  field_simp

/-- **Positive hazard ⇒ strictly decreasing survival in horizon `T`**.
@isnad1 id=strictan.1h2v.s4.f9571974ed4e from=translated src=- shape=6ffa5569 vocab=faca7383
-/
lemma survival_strictAnti_of_pos_hazard {h t : ℝ} (hh : 0 < h) :
    StrictAntiOn (fun T ↦ survivalProbability h t T) (Set.Ici t) := by
  intro T₁ _ T₂ _ hT
  unfold survivalProbability
  have h_arg : -(h * (T₂ - t)) < -(h * (T₁ - t)) := by
    have : h * (T₁ - t) < h * (T₂ - t) := by
      have : T₁ - t < T₂ - t := by linarith
      exact mul_lt_mul_of_pos_left this hh
    linarith
  exact Real.exp_lt_exp.mpr h_arg

/-! ## CDS fair spread with recovery (folded from `CDS.lean`)

A CDS exchanges a periodic premium `c` for `(1 − R)` at default. Under
constant hazard `h` and risk-free rate `r`, both legs share the annuity
factor `(1 − e^{−(r+h) T}) / (r + h)`. Equating PVs gives the fair spread
`c = h · (1 − R)`. Specialises to `c = h` (the bare `creditSpread_eq_hazard`)
at zero recovery. -/

/-- **Fair CDS spread under constant hazard with recovery**: `c = h · (1 − R)`. -/
noncomputable def cdsFairSpread (hh R : ℝ) : ℝ := hh * (1 - R)

/-- **Zero recovery specialisation**: the fair spread equals the hazard rate.
@isnad1 id=eq.0h1v.s3.457cd2ff774e from=translated src=- shape=1fa26838 vocab=4588294e
-/
lemma cdsFairSpread_zero_recovery (hh : ℝ) : cdsFairSpread hh 0 = hh := by
  unfold cdsFairSpread; ring

/-- **Leg-equality characterisation**: with `factor` the common annuity factor,
the fair spread is the unique value equating premium and protection legs.
@isnad1 id=iff.1h4v.s6.d5b98aacca65 from=translated src=- shape=c804d752 vocab=1ae7a10f
-/
theorem cds_leg_equality (hh R factor c : ℝ) (h_factor_ne : factor ≠ 0) :
    c * factor = (1 - R) * hh * factor ↔ c = cdsFairSpread hh R := by
  unfold cdsFairSpread
  constructor
  · intro heq
    have := mul_right_cancel₀ h_factor_ne heq
    linarith
  · intro hc
    rw [hc]; ring

end MathFin
