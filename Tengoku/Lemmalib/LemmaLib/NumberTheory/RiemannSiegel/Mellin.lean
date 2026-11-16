/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Tengoku.Lemmalib.LemmaLib.NumberTheory.RiemannSiegel.Integral
public import Tengoku.Lemmalib.LemmaLib.Analysis.SpecialFunctions.Gamma.ComplexScale
public import Tengoku.Seed.NumberTheory.LSeries.RiemannZeta
public import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Riemann–Siegel integral as `ζ(s)` minus a Gaussian integral

For `Re s > 1` and `0 < c < 1`, the Riemann–Siegel integral `R(s, c)` (`RiemannSiegel.rsIntegral`)
satisfies
`R(s, c) = ζ(s) - ω^s (2π)^s / Γ(s) * ∫₀^∞ y^{s-1} e^{-πy²} / (e^{πωy} - e^{-πωy}) dy`
(`RiemannSiegel.rsIntegral_eq_zeta_sub`), where `ω = e^{iπ/4}`.

The proof is Siegel's: write `w^{-s} = (ω^s / Γ(s)) ∫₀^∞ r^{s-1} e^{-ω w r} dr` on the line (the
Gamma integral with the complex scaling `ω w`, whose real part is positive there), exchange the
integrals, and recognise the inner integral as the Mordell integral `mordell 1 z c` with
`z = i ω r / (2π)`, whose closed form (`Complex.mordell_one`) splits into a geometric series giving
`ζ(s)` and the Gaussian remainder.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-! ### Powers of products -/

/--
@isnad1 id=eq.0h0v.s4.39e2a66a1526 from=translated src=- shape=3c781761 vocab=5fc9f191
-/
theorem arg_rsOmega : arg ω = π / 4 := by
  unfold Complex.rsOmega
  rw [show (π : ℂ) * I / 4 = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I (θ := π / 4)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/--
@isnad1 id=eq.0h0v.s5.519c8c1f1a89 from=translated src=- shape=a3190956 vocab=e6a0cfcf
-/
theorem arg_conj_rsOmega : arg ((starRingEnd ℂ) ω) = -(π / 4) := by
  rw [Complex.arg_conj, arg_rsOmega, ite_eq_right]
  linarith [Real.pi_pos]

/--
@isnad1 id=eq.3h3v.s6.98b074011d9e from=translated src=- shape=4c91d44e vocab=40a5aad0
-/
theorem mul_cpow_of_arg_add_mem {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : arg x + arg y ∈ Ioc (-π) π) (r : ℂ) : (x * y) ^ r = x ^ r * y ^ r := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx hy), Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hy, (Complex.log_mul_eq_add_log_iff hx hy).2 h, add_mul,
    Complex.exp_add]

/-- `w^{-s} = ω^s (ω w)^{-s}` when `Re (ω w) > 0`.
@isnad1 id=eq.1h2v.s6.995a01812ec1 from=translated src=- shape=974de559 vocab=2d7705e0
-/
theorem cpow_neg_eq_rsOmega_cpow_mul {w s : ℂ} (hw : 0 < (ω * w).re) :
    w ^ (-s) = ω ^ s * (ω * w) ^ (-s) := by
  have hb : ω * w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hw0 : w ≠ 0 := right_ne_zero_of_mul hb
  have e : w = (starRingEnd ℂ) ω * (ω * w) := by
    rw [← mul_assoc, conj_rsOmega_mul, one_mul]
  have harg : |arg (ω * w)| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [abs_lt] at harg
  have hc0 : (starRingEnd ℂ) ω ≠ 0 := by
    rw [map_ne_zero]; exact rsOmega_ne_zero
  conv_lhs => rw [e]
  rw [mul_cpow_of_arg_add_mem hc0 hb ⟨by rw [arg_conj_rsOmega]; linarith,
    by rw [arg_conj_rsOmega]; linarith [Real.pi_pos]⟩]
  congr 1
  have hinv : (starRingEnd ℂ) ω = ω⁻¹ := by
    rw [← mul_inv_eq_one₀ (inv_ne_zero rsOmega_ne_zero), inv_inv]; exact conj_rsOmega_mul
  rw [hinv, Complex.inv_cpow _ _ (by rw [arg_rsOmega]; linarith [Real.pi_pos]), Complex.cpow_neg,
    inv_inv]

/--
@isnad1 id=eq.0h2v.s6.a25f82b890ed from=translated src=- shape=ba1dc0e7 vocab=665e4f5a
-/
theorem re_rsOmega_mul_line (c x : ℝ) : (ω * ((c : ℂ) - ω * x)).re = c * (Real.sqrt 2 / 2) := by
  rw [mul_sub, ← mul_assoc, ← sq, rsOmega_sq, rsOmega_eq]
  simp [mul_comm]

/-- The Gamma-integral representation of `w^{-s}` on the Riemann–Siegel line.
@isnad1 id=eq.2h3v.s7.68224c98f967 from=translated src=- shape=edf00672 vocab=2cd667c9
-/
theorem cpow_neg_line_eq_integral {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ((c : ℂ) - ω * x) ^ (-s) = ω ^ s / Complex.Gamma s *
      ∫ r : ℝ in Ioi 0, (r : ℂ) ^ (s - 1) * cexp (-(ω * ((c : ℂ) - ω * x) * r)) := by
  have hre : 0 < (ω * ((c : ℂ) - ω * x)).re := by rw [re_rsOmega_mul_line]; positivity
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hre,
    cpow_neg_eq_rsOmega_cpow_mul hre]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  field_simp

/-! ### Exchanging the integrals -/

/-- The Mordell parameter `z_r = i ω r / (2π)`, for which `e^{-ω w r} = e^{2π i w z_r}`.-/
@[expose] noncomputable def mordellParam (r : ℝ) : ℂ := I * ω * r / (2 * π)

/--
@isnad1 id=eq.0h2v.s6.7c36b839abaa from=translated src=- shape=7091d79b vocab=6ab3e1a6
-/
theorem exp_neg_rsOmega_mul_eq (w : ℂ) (r : ℝ) :
    cexp (-(ω * w * r)) = cexp (2 * π * I * w * mordellParam r) := by
  congr 1
  unfold mordellParam
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [I_sq]
  ring

/--
@isnad1 id=eq.0h2v.s5.6abc202fc341 from=translated src=- shape=cfc91ab0 vocab=5427b6de
-/
theorem exp_mul_kernel_eq_mordellIntegrand (r : ℝ) (u : ℂ) :
    cexp (-(ω * u * r)) * kernel u = mordellIntegrand 1 (mordellParam r) u := by
  rw [exp_neg_rsOmega_mul_eq]
  unfold kernel mordellIntegrand mordellExponent
  rw [mul_div_assoc', ← Complex.exp_add]
  congr 2
  ring

/--
@isnad1 id=continuo.1h1v.s5.ca646ffd3c14 from=translated src=- shape=190c5bb6 vocab=f741b052
-/
theorem continuous_kernel_line {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    Continuous fun x : ℝ => kernel (c - ω * x) := by
  simp_rw [kernel_eq_mordellIntegrand]
  exact continuous_mordellIntegrand_line hc

/--
@isnad1 id=integrab.1h1v.s6.943e96a5d44f from=translated src=- shape=a7b53c57 vocab=b326a350
-/
theorem integrable_kernel_line {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    Integrable fun x : ℝ => kernel (c - ω * x) := by
  simp_rw [kernel_eq_mordellIntegrand]
  exact integrable_mordellIntegrand_line (by simp) hc

/-- The double integrand of Siegel's exchange is integrable on `ℝ × (0, ∞)`.
@isnad1 id=integrab.3h2v.s7.9b0986d23124 from=translated src=- shape=a604e5bb vocab=db2818fd
-/
theorem integrable_uncurry_mellin {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ n : ℤ, c ≠ n) :
    Integrable (Function.uncurry fun (x r : ℝ) =>
        (r : ℂ) ^ (s - 1) * (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hβ : 0 < c * (Real.sqrt 2 / 2) := by positivity
  set G : ℝ × ℝ → ℝ := fun p => ‖kernel (c - ω * p.1)‖ *
    (p.2 ^ (s.re - 1) * Real.exp (-(c * (Real.sqrt 2 / 2)) * p.2)) with hG
  have hGint : Integrable G (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_kernel_line hc).norm.mul_prod
      (Complex.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hβ)
  have hprod : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict ((univ : Set ℝ) ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine hGint.mono' ?_ ?_
  · rw [hprod]
    refine ContinuousOn.aestronglyMeasurable ?_ (MeasurableSet.univ.prod measurableSet_Ioi)
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_of_forall_continuousAt fun p hp => ?_
      have h2 : (0 : ℝ) < p.2 := hp.2
      exact ContinuousAt.comp (g := fun r : ℝ => (r : ℂ) ^ (s - 1))
        (continuousAt_ofReal_cpow_const _ _ (Or.inr h2.ne')) continuous_snd.continuousAt
    · refine Continuous.continuousOn ?_
      refine continuous_const.mul (Continuous.mul (by fun_prop) ?_)
      exact (continuous_kernel_line hc).comp continuous_fst
  · rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    have h2 : (0 : ℝ) < p.2 := hp.2
    obtain ⟨x, r⟩ := p
    simp only [Function.uncurry_apply_pair, hG] at h2 ⊢
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_rsOmega, one_mul,
      norm_cpow_eq_rpow_re_of_pos h2, Complex.norm_exp, sub_re, one_re]
    have e : (-(ω * ((c : ℂ) - ω * x) * r)).re = -(c * (Real.sqrt 2 / 2)) * r := by
      rw [neg_re, Complex.re_mul_ofReal, re_rsOmega_mul_line]; ring
    rw [e]
    exact le_of_eq (by ring)

/-- The inner integral of Siegel's exchange is `r^{s-1} mordell 1 (z_r) c`.
@isnad1 id=eq.0h3v.s7.cf77c387f9b8 from=translated src=- shape=15a1d6f9 vocab=f1a93737
-/
theorem integral_mellin_inner (s : ℂ) (c r : ℝ) :
    ∫ x : ℝ, (r : ℂ) ^ (s - 1) *
        (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))) =
      (r : ℂ) ^ (s - 1) * mordell 1 (mordellParam r) c := by
  rw [integral_const_mul]
  congr 1
  unfold mordell
  congr 1
  ext x
  rw [exp_mul_kernel_eq_mordellIntegrand]

/-- The outer integrand of Siegel's exchange is integrable on `(0, ∞)`.
@isnad1 id=integrab.3h2v.s6.9623b6589954 from=translated src=- shape=fca1b667 vocab=be08b120
-/
theorem integrableOn_cpow_mul_mordell {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ n : ℤ, c ≠ n) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ (s - 1) * mordell 1 (mordellParam r) c) (Ioi 0) := by
  have := (integrable_uncurry_mellin hs hc0 hc).integral_prod_right
  refine this.congr (Eventually.of_forall fun r => ?_)
  exact integral_mellin_inner s c r

/-- Siegel's exchange: `R(s, c) = (ω^s / Γ(s)) ∫₀^∞ r^{s-1} mordell 1 (z_r) c dr`.
@isnad1 id=eq.3h2v.s7.55143c3150c2 from=translated src=- shape=c52c9434 vocab=b974aee5
-/
theorem rsIntegral_eq_integral_mordell {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ n : ℤ, c ≠ n) :
    rsIntegral s c = ω ^ s / Complex.Gamma s *
      ∫ r : ℝ in Ioi 0, (r : ℂ) ^ (s - 1) * mordell 1 (mordellParam r) c := by
  unfold rsIntegral integrand
  have e1 : ∀ x : ℝ, -ω * (((c : ℂ) - ω * x) ^ (-s) * kernel (c - ω * x)) =
      ω ^ s / Complex.Gamma s * ∫ r : ℝ in Ioi 0,
        (r : ℂ) ^ (s - 1) * (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))) := by
    intro x
    rw [cpow_neg_line_eq_integral hs hc0 x]
    simp_rw [show ∀ r : ℝ, (r : ℂ) ^ (s - 1) *
        (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))) =
        (-ω * kernel (c - ω * x)) * ((r : ℂ) ^ (s - 1) * cexp (-(ω * ((c : ℂ) - ω * x) * r)))
      from fun r => by ring]
    rw [integral_const_mul]
    ring
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap (integrable_uncurry_mellin hs hc0 hc)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  exact integral_mellin_inner s c r

/-! ### The closed form of the Mordell integral at the parameter `z_r` -/

/-- The geometric part `e^{-ωr} / (1 - e^{-ωr})` of the Mordell integral at `z_r`.-/
@[expose] noncomputable def geomTerm (r : ℝ) : ℂ := cexp (-(ω * r)) / (1 - cexp (-(ω * r)))

/-- The Gaussian part `e^{-r²/(4π)} / (e^{ωr/2} - e^{-ωr/2})` of the Mordell integral at `z_r`.-/
@[expose] noncomputable def gaussTerm (r : ℝ) : ℂ :=
  cexp (-(r ^ 2 / (4 * π))) / (cexp (ω * r / 2) - cexp (-(ω * r / 2)))

/--
@isnad1 id=eq.0h1v.s5.c8b99eaf6a6c from=translated src=- shape=300f51ce vocab=b9acde6e
-/
theorem re_rsOmega_mul_ofReal (r : ℝ) : (ω * r).re = Real.sqrt 2 / 2 * r := by
  rw [Complex.re_mul_ofReal, rsOmega_eq]; simp

/--
@isnad1 id=lt.1h1v.s5.5e24730b56cc from=translated src=- shape=d8cb7dc5 vocab=c6f8eb4b
-/
theorem norm_exp_neg_rsOmega_mul_lt_one {r : ℝ} (hr : 0 < r) : ‖cexp (-(ω * r))‖ < 1 := by
  rw [Complex.norm_exp, neg_re, re_rsOmega_mul_ofReal, Real.exp_lt_one_iff]
  have : 0 < Real.sqrt 2 := by positivity
  nlinarith

/--
@isnad1 id=ne.1h1v.s5.d3664c7023e3 from=translated src=- shape=4038db59 vocab=1fd6b65a
-/
theorem exp_neg_rsOmega_mul_ne_one {r : ℝ} (hr : 0 < r) : cexp (-(ω * r)) ≠ 1 := by
  intro h
  have := norm_exp_neg_rsOmega_mul_lt_one hr
  rw [h, norm_one] at this
  exact lt_irrefl _ this

/--
@isnad1 id=eq.0h1v.s5.c805c0935cfc from=translated src=- shape=76366e86 vocab=478ae125
-/
theorem two_pi_I_mul_mordellParam (r : ℝ) : 2 * π * I * mordellParam r = -(ω * r) := by
  unfold mordellParam
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [I_sq]
  ring

/--
@isnad1 id=eq.0h1v.s7.52268d04f03e from=translated src=- shape=7e7e3494 vocab=f5783f98
-/
theorem mordellParam_exponent (r : ℝ) :
    -(π * I * mordellParam r ^ 2) + π * I * mordellParam r = -(r ^ 2 / (4 * π)) + -(ω * r / 2) := by
  unfold mordellParam
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (-4 * I * ω ^ 2 * r ^ 2 + 4 * r ^ 2 + 8 * π * ω * r) * I_sq +
    (4 * I * r ^ 2) * rsOmega_sq

/--
@isnad1 id=eq.3h2v.s5.7bcdbcc7179a from=translated src=- shape=5be384c7 vocab=833e6208
-/
theorem mordell_mordellParam {r : ℝ} (hr : 0 < r) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    mordell 1 (mordellParam r) c = geomTerm r - gaussTerm r := by
  have hz : cexp (2 * π * I * mordellParam r) ≠ 1 := by
    rw [two_pi_I_mul_mordellParam]; exact exp_neg_rsOmega_mul_ne_one hr
  rw [Complex.mordell_one hc0 hc1 hz, two_pi_I_mul_mordellParam, mordellParam_exponent,
    Complex.exp_add]
  unfold geomTerm gaussTerm
  have h1 : 1 - cexp (-(ω * r)) ≠ 0 := sub_ne_zero.2 (exp_neg_rsOmega_mul_ne_one hr).symm
  have h2 : cexp (ω * r / 2) - cexp (-(ω * r / 2)) ≠ 0 := by
    have e : cexp (ω * r / 2) - cexp (-(ω * r / 2)) = cexp (ω * r / 2) * (1 - cexp (-(ω * r))) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    rw [e]
    exact mul_ne_zero (Complex.exp_ne_zero _) h1
  have h3 : cexp (ω * r / 2) - cexp (-(ω * r / 2)) = cexp (ω * r / 2) * (1 - cexp (-(ω * r))) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [sub_div, h3]
  congr 1
  have hBC : cexp (-(ω * r / 2)) * cexp (ω * r / 2) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [eq_div_iff (mul_ne_zero (Complex.exp_ne_zero _) h1)]
  calc cexp (-(r ^ 2 / (4 * π))) * cexp (-(ω * r / 2)) / (1 - cexp (-(ω * r))) *
        (cexp (ω * r / 2) * (1 - cexp (-(ω * r))))
      = cexp (-(r ^ 2 / (4 * π))) * (cexp (-(ω * r / 2)) * cexp (ω * r / 2)) *
        ((1 - cexp (-(ω * r))) / (1 - cexp (-(ω * r)))) := by ring
    _ = cexp (-(r ^ 2 / (4 * π))) := by rw [hBC, div_self h1, mul_one, mul_one]

/-! ### The geometric series and `ζ(s)` -/

/--
@isnad1 id=eq.1h1v.s6.64129ce6fd1d from=translated src=- shape=ef6563e3 vocab=c437cba8
-/
theorem geomTerm_eq_tsum {r : ℝ} (hr : 0 < r) :
    geomTerm r = ∑' k : ℕ, cexp (-(((k : ℂ) + 1) * ω * r)) := by
  unfold geomTerm
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one (norm_exp_neg_rsOmega_mul_lt_one hr),
    ← tsum_mul_left]
  congr 1
  ext k
  rw [← pow_succ', ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
@isnad1 id=lt.0h1v.s5.9f7a3c8b98e4 from=translated src=- shape=a15bc95d vocab=bcba1f27
-/
theorem re_nat_add_one_mul_rsOmega (k : ℕ) : 0 < (((k : ℂ) + 1) * ω).re := by
  rw [show ((k : ℂ) + 1) * ω = ω * (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    re_rsOmega_mul_ofReal]
  positivity

/--
@isnad1 id=eq.1h2v.s7.053a01d448b2 from=translated src=- shape=64dac0c5 vocab=be643e06
-/
theorem integral_norm_cpow_mul_geomSummand {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), ‖(r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))‖ =
      (1 / (Real.sqrt 2 / 2)) ^ s.re * ((((k : ℝ) + 1) ^ s.re)⁻¹ * Real.Gamma s.re) := by
  have hβ : 0 < ((k : ℝ) + 1) * (Real.sqrt 2 / 2) := by positivity
  have e : ∀ r ∈ Ioi (0 : ℝ), ‖(r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))‖ =
      r ^ (s.re - 1) * Real.exp (-(((k : ℝ) + 1) * (Real.sqrt 2 / 2) * r)) := by
    intro r hr
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp, sub_re, one_re]
    congr 2
    rw [neg_re, show ((k : ℂ) + 1) * ω * r = ω * ((((k : ℝ) + 1) * r : ℝ) : ℂ) by push_cast; ring,
      re_rsOmega_mul_ofReal]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hβ,
    show 1 / (((k : ℝ) + 1) * (Real.sqrt 2 / 2)) = 1 / (Real.sqrt 2 / 2) * ((k : ℝ) + 1)⁻¹ by
      field_simp,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity)]
  ring

/--
@isnad1 id=summable.1h1v.s7.5c5fb7704734 from=translated src=- shape=b4eddea9 vocab=ab40e11d
-/
theorem summable_integral_norm_cpow_mul_geomSummand {s : ℂ} (hs : 1 < s.re) :
    Summable fun k : ℕ =>
      ∫ r in Ioi (0 : ℝ), ‖(r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))‖ := by
  simp_rw [integral_norm_cpow_mul_geomSummand (by linarith : 0 < s.re)]
  refine Summable.mul_left _ (Summable.mul_right _ ?_)
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hs)
  simpa using this

/--
@isnad1 id=eq.1h2v.s7.78fe72f49b71 from=translated src=- shape=1666e329 vocab=4da54b65
-/
theorem integral_cpow_mul_geomSummand {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r)) =
      ω ^ (-s) * Complex.Gamma s * (1 / ((k : ℂ) + 1) ^ s) := by
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs (re_nat_add_one_mul_rsOmega k)]
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have harg : arg ((k : ℂ) + 1) = 0 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_arg]
  rw [mul_cpow_of_arg_add_mem hk rsOmega_ne_zero
    ⟨by rw [harg, arg_rsOmega]; linarith [Real.pi_pos], by rw [harg, arg_rsOmega]; linarith [Real.pi_pos]⟩,
    Complex.cpow_neg ((k : ℂ) + 1), one_div]
  ring

/-- `∫₀^∞ r^{s-1} e^{-ωr} / (1 - e^{-ωr}) dr = ω^{-s} Γ(s) ζ(s)` for `Re s > 1`.
@isnad1 id=eq.1h1v.s6.dc37c0bedd9a from=translated src=- shape=5085451a vocab=52c833fa
-/
theorem integral_cpow_mul_geomTerm {s : ℂ} (hs : 1 < s.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * geomTerm r =
      ω ^ (-s) * Complex.Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have e : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * geomTerm r =
      ∑' k : ℕ, (r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r)) := by
    intro r hr
    rw [geomTerm_eq_tsum hr, tsum_mul_left]
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    ← integral_tsum_of_summable_integral_norm (fun k => Complex.integrableOn_cpow_mul_exp_neg_mul hs0 (re_nat_add_one_mul_rsOmega k))
      (summable_integral_norm_cpow_mul_geomSummand hs)]
  simp_rw [integral_cpow_mul_geomSummand hs0]
  rw [tsum_mul_left, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-! ### Integrability of the Gaussian part -/

/--
@isnad1 id=le.1h1v.s6.a37e4d949a11 from=translated src=- shape=8cb175cb vocab=14800ebe
-/
theorem norm_exp_sub_exp_neg_rsOmega_half_ge {r : ℝ} (hr : 0 < r) :
    Real.sqrt 2 / 2 * r ≤ ‖cexp (ω * r / 2) - cexp (-(ω * r / 2))‖ := by
  have h1 : ‖cexp (ω * r / 2)‖ = Real.exp (Real.sqrt 2 / 2 * r / 2) := by
    rw [Complex.norm_exp, show ω * r / 2 = ω * ((r / 2 : ℝ) : ℂ) by push_cast; ring,
      re_rsOmega_mul_ofReal]
    ring_nf
  have h2 : ‖cexp (-(ω * r / 2))‖ = Real.exp (-(Real.sqrt 2 / 2 * r / 2)) := by
    rw [Complex.norm_exp, neg_re, show ω * r / 2 = ω * ((r / 2 : ℝ) : ℂ) by push_cast; ring,
      re_rsOmega_mul_ofReal]
    ring_nf
  refine le_trans ?_ (norm_sub_norm_le _ _)
  rw [h1, h2]
  have := abs_le_abs_sinh (Real.sqrt 2 / 2 * r / 2)
  have hpos : 0 < Real.sqrt 2 / 2 * r / 2 := by positivity
  rw [abs_of_pos hpos, abs_of_pos (Real.sinh_pos_iff.2 hpos), Real.sinh_eq] at this
  linarith

/--
@isnad1 id=le.1h1v.s6.8c49f1bcdfaf from=translated src=- shape=6468ca36 vocab=b878d620
-/
theorem norm_gaussTerm_le {r : ℝ} (hr : 0 < r) :
    ‖gaussTerm r‖ ≤ Real.sqrt 2 * r⁻¹ * Real.exp (-(1 / (4 * π)) * r ^ 2) := by
  unfold gaussTerm
  rw [norm_div]
  have hd := norm_exp_sub_exp_neg_rsOmega_half_ge hr
  have hd0 : 0 < Real.sqrt 2 / 2 * r := by positivity
  have hn : ‖cexp (-((r : ℂ) ^ 2 / (4 * π)))‖ = Real.exp (-(1 / (4 * π)) * r ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    rw [show -((r : ℂ) ^ 2 / (4 * π)) = ((-(1 / (4 * π)) * r ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [hn, div_le_iff₀ (lt_of_lt_of_le hd0 hd)]
  calc Real.exp (-(1 / (4 * π)) * r ^ 2)
      = Real.sqrt 2 * r⁻¹ * Real.exp (-(1 / (4 * π)) * r ^ 2) * (Real.sqrt 2 / 2 * r) := by
        have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        field_simp
        linear_combination (-1 : ℝ) * h2
    _ ≤ _ := by gcongr

/--
@isnad1 id=integrab.1h1v.s6.1e440ccbe0ae from=translated src=- shape=a0d51cea vocab=e82da288
-/
theorem integrableOn_cpow_mul_gaussTerm {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ (s - 1) * gaussTerm r) (Ioi 0) := by
  have hb : 0 < 1 / (4 * π) := by positivity
  have hint : IntegrableOn (fun r : ℝ => Real.sqrt 2 *
      (r ^ (s.re - 2) * Real.exp (-(1 / (4 * π)) * r ^ (2 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb).const_mul _
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun r hr => ?_
    rw [mem_Ioi] at hr
    refine (continuousAt_ofReal_cpow_const _ _ (Or.inr hr.ne')).mul ?_
    unfold gaussTerm
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    exact norm_ne_zero_iff.1
      (ne_of_gt (lt_of_lt_of_le (by positivity) (norm_exp_sub_exp_neg_rsOmega_half_ge hr)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [mem_Ioi] at hr
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hr, sub_re, one_re, Real.rpow_two]
    calc r ^ (s.re - 1) * ‖gaussTerm r‖
        ≤ r ^ (s.re - 1) * (Real.sqrt 2 * r⁻¹ * Real.exp (-(1 / (4 * π)) * r ^ 2)) :=
          mul_le_mul_of_nonneg_left (norm_gaussTerm_le hr) (by positivity)
      _ = Real.sqrt 2 * (r ^ (s.re - 2) * Real.exp (-(1 / (4 * π)) * r ^ 2)) := by
          rw [Real.rpow_sub hr, Real.rpow_sub hr, Real.rpow_one, Real.rpow_two]
          field_simp

/--
@isnad1 id=integrab.3h2v.s6.93a70359325d from=translated src=- shape=c81fbead vocab=63f78b94
-/
theorem integrableOn_cpow_mul_geomTerm {s : ℂ} (hs : 1 < s.re) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ (s - 1) * geomTerm r) (Ioi 0) := by
  have h := (integrableOn_cpow_mul_mordell (by linarith) hc0 (ne_int_of_mem_Ioo hc0 hc1)).add
    (integrableOn_cpow_mul_gaussTerm hs)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [mordell_mordellParam hr hc0 hc1]
  ring

/-! ### The substitution `r = 2πy` -/

/-- The Gaussian integral `I₀(s) = ∫₀^∞ y^{s-1} e^{-πy²} / (e^{πωy} - e^{-πωy}) dy`.-/
@[expose] noncomputable def gaussIntegral (s : ℂ) : ℂ :=
  ∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s - 1) *
    (cexp (-(π * y ^ 2)) / (cexp (π * ω * y) - cexp (-(π * ω * y))))

/--
@isnad1 id=eq.0h1v.s6.e0ce4507e903 from=translated src=- shape=4345bee0 vocab=20428cca
-/
theorem gaussTerm_two_pi_mul (y : ℝ) :
    gaussTerm (2 * π * y) = cexp (-(π * y ^ 2)) / (cexp (π * ω * y) - cexp (-(π * ω * y))) := by
  unfold gaussTerm
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  congr 2
  · field_simp
    ring
  · congr 1; ring
  · congr 2; ring

/--
@isnad1 id=eq.0h1v.s6.602f9473836f from=translated src=- shape=7e2b9514 vocab=f75a0bfb
-/
theorem integral_cpow_mul_gaussTerm (s : ℂ) :
    ∫ r : ℝ in Ioi 0, (r : ℂ) ^ (s - 1) * gaussTerm r = (2 * π) ^ s * gaussIntegral s := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have := integral_comp_mul_left_Ioi (fun r : ℝ => (r : ℂ) ^ (s - 1) * gaussTerm r) 0 h2π
  rw [mul_zero] at this
  have hI : ∫ r : ℝ in Ioi 0, (r : ℂ) ^ (s - 1) * gaussTerm r =
      (2 * π : ℂ) * ∫ x : ℝ in Ioi 0, ((2 * π * x : ℝ) : ℂ) ^ (s - 1) * gaussTerm (2 * π * x) := by
    rw [this, Complex.real_smul, ← mul_assoc]
    push_cast
    rw [mul_inv_cancel₀ (by exact_mod_cast h2π.ne'), one_mul]
  rw [hI]
  have e : ∀ x ∈ Ioi (0 : ℝ), ((2 * π * x : ℝ) : ℂ) ^ (s - 1) * gaussTerm (2 * π * x) =
      (2 * π : ℂ) ^ (s - 1) * ((x : ℂ) ^ (s - 1) *
        (cexp (-(π * x ^ 2)) / (cexp (π * ω * x) - cexp (-(π * ω * x))))) := by
    intro x hx
    rw [gaussTerm_two_pi_mul,
      show ((2 * π * x : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) * (x : ℂ) by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg h2π.le (le_of_lt hx)]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
  unfold gaussIntegral
  rw [← mul_assoc]
  congr 1
  rw [Complex.cpow_sub _ _ (by exact_mod_cast h2π.ne'), Complex.cpow_one]
  field_simp

/-! ### The Mellin form of the Riemann–Siegel integral -/

/-- For `Re s > 1` and `0 < c < 1`,
`R(s, c) = ζ(s) - ω^s (2π)^s / Γ(s) * I₀(s)` with `I₀` the Gaussian integral `gaussIntegral`.
@isnad1 id=eq.3h2v.s6.61dfae41b429 from=translated src=- shape=18c0ebce vocab=760dd384
-/
theorem rsIntegral_eq_zeta_sub {s : ℂ} (hs : 1 < s.re) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    rsIntegral s c = riemannZeta s -
      ω ^ s * (2 * π) ^ s / Complex.Gamma s * gaussIntegral s := by
  have hs0 : 0 < s.re := by linarith
  rw [rsIntegral_eq_integral_mordell hs0 hc0 (ne_int_of_mem_Ioo hc0 hc1)]
  have e : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * mordell 1 (mordellParam r) c =
      (r : ℂ) ^ (s - 1) * geomTerm r - (r : ℂ) ^ (s - 1) * gaussTerm r := by
    intro r hr
    rw [mordell_mordellParam hr hc0 hc1, mul_sub]
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_sub (integrableOn_cpow_mul_geomTerm hs hc0 hc1) (integrableOn_cpow_mul_gaussTerm hs),
    integral_cpow_mul_geomTerm hs, integral_cpow_mul_gaussTerm]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hω : ω ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => rsOmega_ne_zero h.1
  rw [Complex.cpow_neg]
  field_simp

end RiemannSiegel
