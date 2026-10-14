/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.HeatBoundaryKernel
public import Tengoku

/-! # Smooth causal extension of the heat boundary kernel

The exponential decay at zero elapsed time absorbs every real power. This
allows the boundary kernel to be extended smoothly by zero at nonpositive
elapsed times, away from the spatial boundary.

## Result

Public entry points include `flatRpow`, `flatRpow_zero`, `flatRpow_smooth`, `flatRpow_neg_three_halves`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Polynomial
open MathFin.FeynmanKacHeatEquation
open scoped Topology ContDiff

/-- The real power `t^p` damped by the smooth glue `expNegInvGlue`, hence zero for `t ≤ 0`. -/
noncomputable def flatRpow (p t : ℝ) : ℝ := t^p * expNegInvGlue t

/--
@isnad1 id=eq.1h2v.s4.30446a4e72b1 from=translated src=- shape=6681cba6 vocab=636a562a
-/
theorem flatRpow_zero {t : ℝ} (ht : t ≤ 0) (p : ℝ) : flatRpow p t = 0 := by
  simp [flatRpow,expNegInvGlue.zero_of_nonpos ht]

/--
@isnad1 id=contdiff.0h1v.s5.f2ede4f66dc9 from=translated src=- shape=0fc4d29f vocab=a5738ba2
-/
theorem flatRpow_smooth (p : ℝ) : ContDiff ℝ ∞ (flatRpow p) := by
  apply contDiff_all_iff_nat.mpr
  intro n
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ)-p)
  have hr : ContDiff ℝ n (fun t : ℝ => t^(p+(m : ℝ))) :=
    Real.contDiff_rpow_const_of_le (by linarith)
  have hg := expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := n) (X^m : ℝ[X])
  convert! hr.mul hg using 1
  funext t
  by_cases ht : 0 < t
  · simp only [flatRpow,eval_pow,eval_X]
    rw [Real.rpow_add ht,Real.rpow_natCast,inv_pow]
    field_simp
  · simp [flatRpow,expNegInvGlue.zero_of_nonpos (le_of_not_gt ht)]

/--
@isnad1 id=eq.1h1v.s6.e98b1434e60e from=translated src=- shape=3ced8822 vocab=7e164dfb
-/
theorem flatRpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    flatRpow (-3/2) t = (t*Real.sqrt t)⁻¹ * Real.exp (-t⁻¹) := by
  unfold flatRpow
  rw [show (-3/2 : ℝ) = -(1+1/2) by norm_num,Real.rpow_neg ht.le,
    Real.rpow_add ht,Real.rpow_one,← Real.sqrt_eq_rpow]
  simp [expNegInvGlue,not_le.mpr ht]

/--
@isnad1 id=eq.1h1v.s6.306df815069f from=translated src=- shape=e98ca390 vocab=d63eb31e
-/
theorem heatBoundaryKernel_unit_flat {t : ℝ} (ht : 0 < t) :
    heatBoundaryKernel t 1 = (2/Real.sqrt Real.pi)*flatRpow (-3/2) (2*t) := by
  rw [flatRpow_neg_three_halves (by positivity)]
  have hs : Real.sqrt (2*Real.pi*t) = Real.sqrt Real.pi * Real.sqrt (2*t) := by
    rw [show 2*Real.pi*t = Real.pi*(2*t) by ring,Real.sqrt_mul Real.pi_pos.le]
  unfold heatBoundaryKernel heatKernel
  rw [hs]
  norm_num only [one_pow,one_div,neg_div]
  field_simp

/-- A causal rewriting of the heat boundary kernel through `flatRpow`, namely
`(x^2)⁻¹*(2/Real.sqrt Real.pi)*flatRpow (-3/2) (2*(t/x^2))`. -/
noncomputable def causalHeatBoundaryKernel (t x : ℝ) : ℝ :=
  (x^2)⁻¹ * (2/Real.sqrt Real.pi) * flatRpow (-3/2) (2*(t/x^2))

/--
@isnad1 id=eq.2h2v.s5.59bd285ba035 from=translated src=- shape=8c7b627f vocab=276f7dd7
-/
theorem causalHeatBoundaryKernel_eq {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    causalHeatBoundaryKernel t x = heatBoundaryKernel t x := by
  have htx : 0 < t/x^2 := div_pos ht (sq_pos_of_pos hx)
  have he := heatBoundaryKernel_scale hx htx
  have hc : x^2*(t/x^2) = t := by field_simp
  rw [hc] at he
  unfold causalHeatBoundaryKernel
  rw [mul_assoc,← heatBoundaryKernel_unit_flat htx,← he]
  field_simp

/--
@isnad1 id=eq.1h2v.s4.9bbbab8f54b9 from=translated src=- shape=15cdfb60 vocab=1aefebc8
-/
theorem causalHeatBoundaryKernel_zero {t x : ℝ} (ht : t ≤ 0) :
    causalHeatBoundaryKernel t x = 0 := by
  unfold causalHeatBoundaryKernel
  rw [flatRpow_zero (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    (div_nonpos_of_nonpos_of_nonneg ht (sq_nonneg x))),mul_zero]

/--
@isnad1 id=contdiff.1h2v.s6.cbdd7b3173a5 from=translated src=- shape=9df5aed9 vocab=b4f81ccd
-/
theorem causalHeatBoundaryKernel_smoothAt {t x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => causalHeatBoundaryKernel z.1 z.2) (t,x) := by
  have hs : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (z.2^2)⁻¹) (t,x) :=
    (contDiffAt_snd.pow 2).inv (pow_ne_zero 2 hx)
  exact (hs.mul contDiffAt_const).mul ((flatRpow_smooth (-3/2)).contDiffAt.comp (t,x)
    (contDiffAt_const.mul (contDiffAt_fst.div (contDiffAt_snd.pow 2) (pow_ne_zero 2 hx))))

/--
@isnad1 id=le.1h2v.s4.adfccbb1ab27 from=translated src=- shape=676e8bff vocab=e396f428
-/
theorem causalHeatBoundaryKernel_nonneg (t : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ causalHeatBoundaryKernel t x := by
  rcases le_or_gt t 0 with ht | ht
  · rw [causalHeatBoundaryKernel_zero ht]
  · rw [causalHeatBoundaryKernel_eq ht hx]
    exact (heatBoundaryKernel_pos ht hx).le

/-- The causal kernel solves the PDE even at zero elapsed time, away from x=0.
@isnad1 id=eq.1h2v.s7.8930f35db1d5 from=translated src=- shape=7ce6a63d vocab=2bb82812
-/
theorem causalHeatBoundaryKernel_equation (t : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (fun s => causalHeatBoundaryKernel s x) t =
      (1/2)*deriv (deriv (causalHeatBoundaryKernel t)) x := by
  rcases le_or_gt t 0 with ht | ht
  · have hm : IsLocalMin (fun s => causalHeatBoundaryKernel s x) t := by
      apply Eventually.of_forall
      intro s
      change causalHeatBoundaryKernel t x ≤ causalHeatBoundaryKernel s x
      rw [causalHeatBoundaryKernel_zero ht]
      exact causalHeatBoundaryKernel_nonneg s hx
    rw [hm.deriv_eq_zero]
    have he : causalHeatBoundaryKernel t = fun _ => 0 :=
      funext fun _ => causalHeatBoundaryKernel_zero ht
    simp [he]
  · have htime : (fun s => causalHeatBoundaryKernel s x) =ᶠ[𝓝 t]
        (fun s => heatBoundaryKernel s x) := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact causalHeatBoundaryKernel_eq hs hx
    have hspace : causalHeatBoundaryKernel t =ᶠ[𝓝 x] heatBoundaryKernel t := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact causalHeatBoundaryKernel_eq ht hy
    rw [htime.deriv_eq,hspace.deriv.deriv_eq]
    exact heatBoundaryKernel_equation ht x

end MathFin.BlackScholes.AmericanPut.Stopping
