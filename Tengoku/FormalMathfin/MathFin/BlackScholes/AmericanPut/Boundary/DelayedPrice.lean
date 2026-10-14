/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.ObstacleComparison

/-! # A clamped time delay of the price

The delay equals the initial payoff before its clock starts. Whenever it
exceeds the payoff, its delayed time is positive and it is in continuation.
Thus the pricing equation and local smoothness are available exactly where
an obstacle comparison can have a positive contact.

## Result

Public entry points include `delayedPrice`, `delayedPrice_eventuallyEq`, `delayedPrice_continuous`, `delayedPrice_initial`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- The price on a clock delayed by `a` and clamped at zero: `p x (max (t - a) 0)`. -/
noncomputable def delayedPrice (p : ℝ → ℝ → ℝ) (a x t : ℝ) : ℝ :=
  p x (max (t-a) 0)

/--
@isnad1 id=eventual.1h4v.s6.10a33e3be2e9 from=translated src=- shape=2b3cb376 vocab=a437239a
-/
theorem delayedPrice_eventuallyEq {p : ℝ → ℝ → ℝ} {a x t : ℝ} (ht : a < t) :
    (fun z : ℝ × ℝ => delayedPrice p a z.1 z.2) =ᶠ[𝓝 (x,t)]
      (fun z => p z.1 (z.2-a)) := by
  have he : ∀ᶠ z : ℝ × ℝ in 𝓝 (x,t), a < z.2 :=
    continuousAt_const.eventually_lt continuousAt_snd ht
  filter_upwards [he] with z hz
  simp [delayedPrice,max_eq_left (sub_nonneg.mpr hz.le)]

namespace DividendPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/--
@isnad1 id=continuo.1h5v.s5.ba824ead3a8c from=translated src=- shape=e7fad0a2 vocab=b8e728af
-/
theorem delayedPrice_continuous (hp : DividendPutSolution k h p b) (a : ℝ) :
    Continuous (fun z : ℝ × ℝ => delayedPrice p a z.1 z.2) := by
  exact hp.price_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (z.1,max (z.2-a) 0)) by fun_prop)
    (fun z => le_max_right (z.2-a) 0)

/--
@isnad1 id=eq.2h6v.s5.ea916e37a2b6 from=translated src=- shape=8d1a5941 vocab=cc775a23
-/
theorem delayedPrice_initial (hp : DividendPutSolution k h p b) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    delayedPrice p a x 0 = putPayoff x := by
  simp only [delayedPrice,zero_sub,max_eq_right (neg_nonpos.mpr ha),hp.initial]

/--
@isnad1 id=and.2h7v.s5.970d37ab736c from=translated src=- shape=d75cb403 vocab=fb47994a
-/
theorem delayedPrice_above_payoff (hp : DividendPutSolution k h p b) {a x t : ℝ}
    (hgt : putPayoff x < delayedPrice p a x t) : a < t ∧ b (t-a) < x := by
  have ht : a < t := by
    by_contra hn
    have he : max (t-a) 0 = 0 := max_eq_right (by linarith)
    simp [delayedPrice,he,hp.initial] at hgt
  refine ⟨ht,?_⟩
  by_contra hn
  have hxb : x ≤ b (t-a) := le_of_not_gt hn
  have he : delayedPrice p a x t = 1-Real.exp x := by
    simp only [delayedPrice,max_eq_left (sub_nonneg.mpr ht.le)]
    exact hp.exercise x (t-a) (sub_pos.mpr ht) hxb
  rw [he] at hgt
  exact (not_lt_of_ge (le_max_left (1-Real.exp x) 0)) hgt

/--
@isnad1 id=contdiff.3h7v.s7.ef6a4c2ffd89 from=translated src=- shape=f528f4f4 vocab=b0ebb303
-/
theorem delayedPrice_contDiffAt (hp : DividendPutSolution k h p b) {a x t : ℝ}
    (ht : a < t) (hx : b (t-a) < x) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => delayedPrice p a z.1 z.2) (x,t) := by
  have hs : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => p z.1 z.2) (x,t-a) :=
    (hp.price_contDiffAt (sub_pos.mpr ht) hx).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => p z.1 (z.2-a)) (x,t) := by
    simpa only [Function.comp_def] using hs.comp (x,t)
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (z.1,z.2-a)) (x,t) by fun_prop)
  exact hc.congr_of_eventuallyEq (delayedPrice_eventuallyEq ht)

/--
@isnad1 id=eq.3h7v.s6.8493526b97ef from=translated src=- shape=f8bbb9b7 vocab=a273c518
-/
theorem delayedPrice_equation (hp : DividendPutSolution k h p b) {a x t : ℝ}
    (ht : a < t) (hx : b (t-a) < x) :
    deriv (delayedPrice p a x) t = dividendSpatialOperator k h (fun y => delayedPrice p a y t) x := by
  have hs : DifferentiableAt ℝ (p x) (t-a) :=
    ((hp.price_contDiffAt (sub_pos.mpr ht) hx).comp (t-a)
      (show ContDiffAt ℝ ∞ (fun s : ℝ => (x,s)) (t-a) by fun_prop)).differentiableAt (by simp)
  have he : delayedPrice p a x =ᶠ[𝓝 t] (fun s => p x (s-a)) :=
    (delayedPrice_eventuallyEq (p := p) (x := x) ht).comp_tendsto
      (continuousAt_const.prodMk continuousAt_id)
  have hd : HasDerivAt (delayedPrice p a x) (deriv (p x) (t-a)) t := by
    have hc := hs.hasDerivAt.comp t ((hasDerivAt_id t).sub_const a)
    have hh : HasDerivAt (fun s => p x (s-a)) (deriv (p x) (t-a)) t := by
      simpa only [Function.comp_def,id_eq,mul_one] using hc
    exact hh.congr_of_eventuallyEq he
  have hslice : (fun y => delayedPrice p a y t) = fun y => p y (t-a) := by
    funext y
    simp [delayedPrice,max_eq_left (sub_nonneg.mpr ht.le)]
  rw [hd.deriv,hslice]
  exact hp.equation x (t-a) (sub_pos.mpr ht) hx

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
