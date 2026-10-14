/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.ClassicalContact

/-!
# The Brownian-coordinate PDE of the discounted classical-price candidate

Inside continuation, physical elapsed time and the Brownian spatial coordinate
turn the normalized pricing equation into `F_t + (1/2) F_ww = 0`.
All differentiability statements are local to continuation. No smoothness at
the exercise boundary, or martingale consequence of Ito's formula, is assumed.

## Result

Public entry points include `brownianPriceKernel`, `affinePrice_hasDeriv_time`, `brownianPriceKernel_hasDeriv_time`, `brownianPriceKernel_deriv_space`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MathFin.BlackScholes.AmericanPut.Boundary
open scoped ContDiff NNReal

/-- The discounted classical price `K*p` read in physical time `t` and Brownian coordinate `w`:
log spot `x₀+(r-q-σ^2/2)*t+σ*w`, remaining normalized time `σ^2/2*(T-t)`, discount
`exp (-r*t)`. -/
noncomputable def brownianPriceKernel (p : ℝ → ℝ → ℝ) (K r q σ x₀ T t w : ℝ) : ℝ :=
  Real.exp (-r*t)*(K*p (x₀+(r-q-σ^2/2)*t+σ*w) (σ^2/2*(T-t)))

/--
@isnad1 id=hasderiv.1h8v.s8.4681d74d95bd from=translated src=- shape=55419274 vocab=0288a250
-/
theorem affinePrice_hasDeriv_time {p : ℝ → ℝ → ℝ} {x₀ β σ a T t w : ℝ}
    (hp : DifferentiableAt ℝ (fun z : ℝ × ℝ => p z.1 z.2) (x₀+β*t+σ*w,a*(T-t))) :
    HasDerivAt (fun s => p (x₀+β*s+σ*w) (a*(T-s)))
      (β*deriv (fun x => p x (a*(T-t))) (x₀+β*t+σ*w) -
        a*deriv (p (x₀+β*t+σ*w)) (a*(T-t))) t := by
  let x := x₀+β*t+σ*w
  let u := a*(T-t)
  let A := fderiv ℝ (fun z : ℝ × ℝ => p z.1 z.2) (x,u)
  have hA : HasFDerivAt (fun z : ℝ × ℝ => p z.1 z.2) A (x,u) := hp.hasFDerivAt
  have hx : HasDerivAt (fun y => p y u) (A (1,0)) x := by
    simpa only [Function.comp_def,id_eq] using
      hA.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x u))
  have hu : HasDerivAt (p x) (A (0,1)) u := by
    simpa only [Function.comp_def,id_eq] using
      hA.comp_hasDerivAt u ((hasDerivAt_const u x).prodMk (hasDerivAt_id u))
  have hpath : HasDerivAt (fun s : ℝ => (x₀+β*s+σ*w,a*(T-s))) (β,-a) t := by
    convert! ((((hasDerivAt_id t).const_mul β).const_add x₀).add_const (σ*w)).prodMk
      (((hasDerivAt_const t T).sub (hasDerivAt_id t)).const_mul a) using 1
    simp
  change HasDerivAt _ (β*deriv (fun y => p y u) x-a*deriv (p x) u) t
  rw [hx.deriv,hu.deriv]
  convert! hA.comp_hasDerivAt t hpath using 1
  rw [show ((β,-a) : ℝ × ℝ) = β • (1,0)-a • (0,1) by ext <;> simp]
  simp only [map_sub,map_smul,smul_eq_mul]

/--
@isnad1 id=hasderiv.1h9v.s9.821dd63d76a2 from=translated src=- shape=6b395deb vocab=75dbd650
-/
theorem brownianPriceKernel_hasDeriv_time {p : ℝ → ℝ → ℝ} {K r q σ x₀ T t w : ℝ}
    (hp : DifferentiableAt ℝ (fun z : ℝ × ℝ => p z.1 z.2)
      (x₀+(r-q-σ^2/2)*t+σ*w,σ^2/2*(T-t))) :
    HasDerivAt (fun s => brownianPriceKernel p K r q σ x₀ T s w)
      (Real.exp (-r*t)*K*((r-q-σ^2/2)*
        deriv (fun x => p x (σ^2/2*(T-t))) (x₀+(r-q-σ^2/2)*t+σ*w) -
        σ^2/2*deriv (p (x₀+(r-q-σ^2/2)*t+σ*w)) (σ^2/2*(T-t)) -
        r*p (x₀+(r-q-σ^2/2)*t+σ*w) (σ^2/2*(T-t)))) t := by
  convert! (((hasDerivAt_id t).const_mul (-r)).exp).mul
    ((affinePrice_hasDeriv_time hp).const_mul K) using 1
  dsimp [brownianPriceKernel]
  ring

/--
@isnad1 id=eq.0h9v.s8.9f66d0058920 from=translated src=- shape=132d9fc3 vocab=1e339498
-/
theorem brownianPriceKernel_deriv_space (p : ℝ → ℝ → ℝ) (K r q σ x₀ T t w : ℝ) :
    deriv (fun y => brownianPriceKernel p K r q σ x₀ T t y) w =
      Real.exp (-r*t)*K*σ*deriv (fun x => p x (σ^2/2*(T-t))) (x₀+(r-q-σ^2/2)*t+σ*w) := by
  simp only [brownianPriceKernel,deriv_const_mul_field]
  rw [show (fun y => p (x₀+(r-q-σ^2/2)*t+σ*y) (σ^2/2*(T-t))) =
    (fun y => (fun x => p (x₀+(r-q-σ^2/2)*t+x) (σ^2/2*(T-t))) (σ*y)) from rfl]
  rw [deriv_comp_mul_left σ (fun x => p (x₀+(r-q-σ^2/2)*t+x) (σ^2/2*(T-t))) w,
    deriv_comp_const_add (fun x => p x (σ^2/2*(T-t))) (x₀+(r-q-σ^2/2)*t) (σ*w)]
  simp only [smul_eq_mul]
  ring

/--
@isnad1 id=eq.0h9v.s8.6054ef3602e8 from=translated src=- shape=b43cfabb vocab=1e339498
-/
theorem brownianPriceKernel_deriv2_space (p : ℝ → ℝ → ℝ) (K r q σ x₀ T t w : ℝ) :
    deriv (deriv (fun y => brownianPriceKernel p K r q σ x₀ T t y)) w =
      Real.exp (-r*t)*K*σ^2*deriv (deriv (fun x => p x (σ^2/2*(T-t))))
        (x₀+(r-q-σ^2/2)*t+σ*w) := by
  rw [show deriv (fun y => brownianPriceKernel p K r q σ x₀ T t y) =
    fun y => Real.exp (-r*t)*K*σ*deriv (fun x => p x (σ^2/2*(T-t))) (x₀+(r-q-σ^2/2)*t+σ*y)
    from funext (brownianPriceKernel_deriv_space p K r q σ x₀ T t)]
  rw [deriv_const_mul_field]
  rw [show (fun y => deriv (fun x => p x (σ^2/2*(T-t))) (x₀+(r-q-σ^2/2)*t+σ*y)) =
    (fun y => (fun v => deriv (fun x => p x (σ^2/2*(T-t))) (x₀+(r-q-σ^2/2)*t+v)) (σ*y)) from rfl]
  rw [deriv_comp_mul_left σ (fun v => deriv (fun x => p x (σ^2/2*(T-t)))
    (x₀+(r-q-σ^2/2)*t+v)) w,deriv_comp_const_add]
  simp only [smul_eq_mul]
  ring

/--
@isnad1 id=contdiff.4h10v.s8.2b13768893c3 from=translated src=- shape=7e86c7c6 vocab=43e6b655
-/
theorem brownianPriceKernel_contDiffAt {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    {K r q σ x₀ T t w : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hσ : 0 < σ) (ht : t < T)
    (hx : b (σ^2/2*(T-t)) < x₀+(r-q-σ^2/2)*t+σ*w) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => brownianPriceKernel p K r q σ x₀ T z.1 z.2) (t,w) := by
  have htime : 0 < σ^2/2*(T-t) := mul_pos (by positivity) (sub_pos.mpr ht)
  have hcomp : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
      p (x₀+(r-q-σ^2/2)*z.1+σ*z.2) (σ^2/2*(T-z.1))) (t,w) := by
    simpa only [Function.comp_def] using (hp.price_contDiffAt htime hx).comp (t,w)
      (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
        (x₀+(r-q-σ^2/2)*z.1+σ*z.2,σ^2/2*(T-z.1))) (t,w) by fun_prop)
  exact (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.exp (-r*z.1)) (t,w) by fun_prop).mul
    (contDiffAt_const.mul hcomp)

/-- The exact normalized pricing equation cancels the physical discounted
Brownian drift. This is asserted only inside continuation, not at its edge.
@isnad1 id=eq.4h10v.s8.7a0692d7c057 from=translated src=- shape=654f6ee8 vocab=6bcfb03a
-/
theorem brownianPriceKernel_heat_equation {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    {K r q σ x₀ T t w : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hσ : 0 < σ) (ht : t < T)
    (hx : b (σ^2/2*(T-t)) < x₀+(r-q-σ^2/2)*t+σ*w) :
    deriv (fun s => brownianPriceKernel p K r q σ x₀ T s w) t +
      (1/2)*deriv (deriv (fun y => brownianPriceKernel p K r q σ x₀ T t y)) w = 0 := by
  have htime : 0 < σ^2/2*(T-t) := mul_pos (by positivity) (sub_pos.mpr ht)
  rw [(brownianPriceKernel_hasDeriv_time
    ((hp.price_contDiffAt htime hx).differentiableAt (by simp))).deriv,
    brownianPriceKernel_deriv2_space,hp.equation _ _ htime hx]
  unfold dividendSpatialOperator normalizedRate
  field_simp
  ring

/--
@isnad1 id=eq.1h11v.s6.beed03c94abb from=translated src=- shape=99fc5797 vocab=1c87985b
-/
theorem classicalCandidate_eq_kernel {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (p : ℝ → ℝ → ℝ) (K r q σ S : ℝ) {T t : ℝ≥0} (ht : t ≤ T) (outcome : Ω) :
    classicalCandidate W K r q σ S p T t outcome =
      brownianPriceKernel p K r q σ (Real.log (S/K)) T t (W t outcome) := by
  simp only [classicalCandidate,brownianPriceKernel,classicalLogSpot,min_eq_left ht]

end MathFin.BlackScholes.AmericanPut.Stopping
