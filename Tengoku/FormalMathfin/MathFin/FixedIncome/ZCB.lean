/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

/-!
# Fixed-income basics under a deterministic short rate

Closed-form identities for a zero-coupon bond with continuous compounding under
a constant short rate `r`:

  `B(t, T) = exp(-(r · (T - t)))`.

Results:

* `zcb_at_maturity`: `B(T, T) = 1`.
* `zcb_yield_eq_rate`: under a constant `r`, the yield-to-maturity equals `r`.
* `hasDerivAt_zcb_r`: `∂_r B(t, T) = -(T - t) · B(t, T)` — the bond duration is
  the time-to-maturity.
* `zcb_duration_eq_time_to_maturity`: `-∂_r B / B = T - t`.
* `hasDerivAt_zcb_r_r`: second-derivative identity giving convexity
  `∂²_r B / B = (T - t)²`.

The model is purely deterministic; the Vasicek / CIR / HJM stochastic versions
would need Itô calculus.
-/

@[expose] public section

namespace MathFin

open Real

/-- Continuous-compounding zero-coupon bond price under a constant short rate. -/
noncomputable def zcb (r : ℝ) (t T : ℝ) : ℝ := Real.exp (-(r * (T - t)))

/-- The bond pays `1` at maturity.
@isnad1 id=eq.0h2v.s4.0361f3010b6f from=translated src=- shape=c2a510d9 vocab=db5d6c60
-/
lemma zcb_at_maturity (r T : ℝ) : zcb r T T = 1 := by
  unfold zcb
  rw [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- The bond is positive.
@isnad1 id=lt.0h3v.s4.053993e83024 from=translated src=- shape=ac9c39a3 vocab=5af4342e
-/
lemma zcb_pos (r t T : ℝ) : 0 < zcb r t T := Real.exp_pos _

/-- Yield-to-maturity for a ZCB under a constant rate equals the rate.
@isnad1 id=eq.1h3v.s5.d9db939cec47 from=translated src=- shape=6e13cf87 vocab=2608282d
-/
lemma zcb_yield_eq_rate {r t T : ℝ} (htT : t < T) :
    -Real.log (zcb r t T) / (T - t) = r := by
  unfold zcb
  rw [Real.log_exp, neg_neg]
  have h_ne : T - t ≠ 0 := sub_ne_zero.mpr htT.ne'
  field_simp

/-- `∂_r B(t, T) = -(T - t) · B(t, T)`. Duration of a ZCB equals time-to-maturity.
@isnad1 id=hasderiv.0h3v.s6.51e0b24fd614 from=translated src=- shape=710b2ed3 vocab=bba4f7d7
-/
lemma hasDerivAt_zcb_r (t T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' ↦ zcb r' t T) (-(T - t) * zcb r t T) r := by
  unfold zcb
  have h_lin : HasDerivAt (fun r' : ℝ ↦ -(r' * (T - t))) (-(T - t)) r := by
    have h := (hasDerivAt_id r).mul_const (T - t)
    rw [one_mul] at h
    exact h.neg
  have h := h_lin.exp
  convert h using 1
  ring

/-- ZCB Macaulay duration equals time-to-maturity: `-∂_r B / B = T - t`.
@isnad1 id=eq.0h3v.s5.6064a6d25ba7 from=translated src=- shape=15669e99 vocab=db0f9798
-/
lemma zcb_duration_eq_time_to_maturity (t T r : ℝ) :
    -(-(T - t) * zcb r t T) / zcb r t T = T - t := by
  have h_ne : zcb r t T ≠ 0 := (zcb_pos r t T).ne'
  field_simp

/-- `∂²_r B(t, T) = (T - t)² · B(t, T)`. Convexity = (time-to-maturity)².
@isnad1 id=hasderiv.0h3v.s6.1bba9f4b9735 from=translated src=- shape=15f2b221 vocab=e4fd1022
-/
lemma hasDerivAt_zcb_r_r (t T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' ↦ -(T - t) * zcb r' t T) ((T - t)^2 * zcb r t T) r := by
  have h := (hasDerivAt_zcb_r t T r).const_mul (-(T - t))
  rw [show (T - t) ^ 2 * zcb r t T = -(T - t) * (-(T - t) * zcb r t T) from by ring]
  exact h

/-- ZCB convexity = squared time-to-maturity: `∂²_r B / B = (T - t)²`.
@isnad1 id=eq.0h3v.s6.4885366184ee from=translated src=- shape=4bce8551 vocab=ee37d03e
-/
lemma zcb_convexity_eq_time_to_maturity_sq (t T r : ℝ) :
    ((T - t)^2 * zcb r t T) / zcb r t T = (T - t)^2 := by
  have h_ne : zcb r t T ≠ 0 := (zcb_pos r t T).ne'
  field_simp

end MathFin
