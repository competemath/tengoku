/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.Seed.MeasureTheory.Measure.CharacteristicFunction.Basic
import Tengoku.Seed.Probability.Distributions.Gaussian.Real
import Tengoku.Seed.MeasureTheory.Measure.GiryMonad
import Tengoku.Seed.MeasureTheory.Measure.ProbabilityMeasure
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Transform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Brownian laws and their density

Home: line/cone:lem:bridge-exponents

The objects `lem:bridge-exponents` is written in (`BridgeExponents`), and the elementary facts its
proof reads: `brownianLaw u = g_u` is Mathlib's `gaussianReal 0 u`, and `brownianDensity u x =
g_u(x)` its density; both are thin wrappers whose only job is to let the bridge equations be
written with `u` a real time rather than an `ℝ≥0` variance. At `u = 0` the wrapper is `δ₀`, and
for `u < 0` it is junk — every statement quantifies over `u > 0` or integrates over `(0,∞)`.

Moved from the spatial article's export (`SpatialLine.BrownianDensity`, and from
`SpatialLine.TransformBridge` the fact that computes the cosine transform at a Gaussian, at
`cone-v0.1`), statements unchanged up to the namespace. The cosine transform `fourierCos` itself,
with `integrable_charFun_integrand` and `fourierCos_eq_charFun_re`, is `ScaleSpaceCore.Transform`'s
(Q-0301, merged first; the two moves had carried identical copies). The first move took only
what `bridge_exponents` needs; the mixture facts about `Measure.bind brownianLaw` that the
Gaussian variance mixtures read followed (Q-0363: `measurable_brownianLaw`,
`isProbabilityMeasure_bind_brownianLaw`, `fourierCos_bind_brownianLaw`, from the same module at
`cone-v0.1`, statements unchanged up to the namespace). `isSymmetric_bind_brownianLaw` stayed
behind: no second consumer reads it.

## The mixtures

`Measure.bind brownianLaw` mixes the Gaussian laws against a law on the delay. It is a
probability measure, and `fourierCos_bind_brownianLaw` says its cosine transform at `ω` is the
Laplace transform of the delay law at `ω²/2`.

## The two elementary bounds

`brownianDensity_div_le` bounds `g_u(x)/u` by `16/x⁴` uniformly for `u` in `(0,1]`, which is
where the Gaussian's flatness at `u = 0` pays for a missing power of `u` in a mixture carrying
`du/u`; above `1` the density is at most `1` (`brownianDensity_le_one`).
-/

namespace ScaleSpace

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The cosine transform at a Gaussian -/

/-- **The cosine transform of a centred Gaussian law of variance `v`**, `e^{-vω²/2}`.
@isnad1 id=eq.0h2v.s6.4d6ccbdfdcaf from=translated src=- shape=a41e5081 vocab=eae97ac9
-/
theorem fourierCos_gaussianReal (v : NNReal) (ω : ℝ) :
    fourierCos (ProbabilityTheory.gaussianReal 0 v) ω = Real.exp (-((v : ℝ) * ω ^ 2 / 2)) := by
  rw [fourierCos_eq_charFun_re, ProbabilityTheory.charFun_gaussianReal]
  have harg : (ω : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2
      = (((-((v : ℝ) * ω ^ 2 / 2)) : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_exp, Complex.ofReal_re]

/-! ## The Brownian laws -/

/-- **`g_u`**, the law of Brownian motion at time `u`: the centred Gaussian of variance `u`,
with `g_0 = δ_0`.-/
noncomputable def brownianLaw (u : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 u.toNNReal

/-- **`g_u(x)`**, the density of `brownianLaw u` for `u > 0`.-/
noncomputable def brownianDensity (u x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 u.toNNReal x

/-- **`brownianLaw` is a measurable family of measures.**
@isnad1 id=measurab.0h0v.s3.46b4f4526b98 from=translated src=- shape=1bdc2383 vocab=deb31202
-/
theorem measurable_brownianLaw : Measurable brownianLaw := by
  unfold brownianLaw
  fun_prop

/-! ## The Brownian density, explicitly -/

/-- `g_u(x) = (2πu)^{-1/2}e^{-x²/2u}` at every positive time.
@isnad1 id=eq.1h2v.s6.ef32293da728 from=translated src=- shape=b8dd8676 vocab=529279bf
-/
theorem brownianDensity_eq {u : ℝ} (hu : 0 < u) (x : ℝ) :
    brownianDensity u x = (Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-x ^ 2 / (2 * u)) := by
  unfold brownianDensity gaussianPDFReal
  rw [Real.coe_toNNReal _ hu.le]
  norm_num

/--
@isnad1 id=le.0h2v.s4.e1606709bce8 from=translated src=- shape=a120b2a8 vocab=e35bb2fa
-/
theorem brownianDensity_nonneg (u x : ℝ) : 0 ≤ brownianDensity u x :=
  gaussianPDFReal_nonneg _ _ _

/--
@isnad1 id=measurab.0h1v.s3.fd90c1d47c93 from=translated src=- shape=f736e2c1 vocab=08c56d90
-/
theorem measurable_brownianDensity (u : ℝ) : Measurable (brownianDensity u) := by
  unfold brownianDensity; fun_prop

/--
@isnad1 id=measurab.0h1v.s3.b9b1dec0f10a from=translated src=- shape=b33faf8c vocab=08c56d90
-/
theorem measurable_brownianDensity_time (x : ℝ) :
    Measurable fun u : ℝ => brownianDensity u x := by
  unfold brownianDensity gaussianPDFReal; fun_prop

/--
@isnad1 id=measurab.0h0v.s4.0d20e79591b6 from=translated src=- shape=57a5edaf vocab=3cd07729
-/
theorem measurable_brownianDensity_uncurry : Measurable (Function.uncurry brownianDensity) := by
  unfold brownianDensity gaussianPDFReal Function.uncurry; fun_prop

/-- `g_u` is even.
@isnad1 id=eq.0h2v.s3.38bde54adc02 from=translated src=- shape=6be742d9 vocab=1b7fd6ba
-/
theorem brownianDensity_neg (u x : ℝ) : brownianDensity u (-x) = brownianDensity u x := by
  unfold brownianDensity gaussianPDFReal; simp

/--
@isnad1 id=eq.1h1v.s5.23eefd60e56c from=translated src=- shape=a3eca677 vocab=4952ce8e
-/
theorem brownianLaw_eq_withDensity {u : ℝ} (hu : 0 < u) :
    brownianLaw u = volume.withDensity fun x => ENNReal.ofReal (brownianDensity u x) := by
  unfold brownianLaw brownianDensity
  rw [gaussianReal_of_var_ne_zero _ (by positivity)]
  rfl

/-! ## Two elementary bounds on the density -/

/-- `y² ≤ 4e^y` for `y ≥ 0`: the second-order term of the exponential series, in the form the
near-origin bound uses.
@isnad1 id=le.1h1v.s5.18ed4e0cc3e3 from=translated src=- shape=df01aa36 vocab=fc917557
-/
theorem sq_le_four_mul_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ 4 * Real.exp y := by
  have h := Real.add_one_le_exp (y / 2)
  have h2 : Real.exp (y / 2) ^ 2 = Real.exp y := by
    rw [← Real.exp_nat_mul]; norm_num; ring_nf
  nlinarith [Real.exp_pos (y / 2), h, h2]

/-- **The near-origin bound.** `g_u(x)/u ≤ 16/x⁴` for `0 < u ≤ 1` and `x ≠ 0`.

This is what lets the mixture integrand, which carries `du/u`, be dominated on `(0,1)` by a
multiple of `k_I(u)` — the *first* integrability field of `def:causal-admissible`, which
carries no `u⁻¹`. The Gaussian's flatness at `u = 0` pays for the missing power.
@isnad1 id=le.3h2v.s6.458dacc51114 from=translated src=- shape=81ac2eab vocab=2d39dfb0
-/
theorem brownianDensity_div_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {x : ℝ} (hx : x ≠ 0) :
    brownianDensity u x / u ≤ 16 / x ^ 4 := by
  have hpi := Real.two_le_pi
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  have hy : (0 : ℝ) ≤ x ^ 2 / (2 * u) := by positivity
  have hpos : (0 : ℝ) < Real.exp (x ^ 2 / (2 * u)) := Real.exp_pos _
  have h := sq_le_four_mul_exp hy
  have hsq : (x ^ 2 / (2 * u)) ^ 2 = x ^ 4 / (4 * u ^ 2) := by field_simp; ring
  rw [hsq, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * u ^ 2)] at h
  have hexp : Real.exp (-x ^ 2 / (2 * u)) ≤ 16 * u ^ 2 / x ^ 4 := by
    have hinv : Real.exp (-x ^ 2 / (2 * u)) = (Real.exp (x ^ 2 / (2 * u)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hinv, inv_le_iff_one_le_mul₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hx4]
    nlinarith [h]
  have hsqrt : u ≤ Real.sqrt (2 * Real.pi * u) := by
    have hle : u ^ 2 ≤ 2 * Real.pi * u := by nlinarith
    calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0.le).symm
      _ ≤ Real.sqrt (2 * Real.pi * u) := Real.sqrt_le_sqrt hle
  have hspos : (0 : ℝ) < Real.sqrt (2 * Real.pi * u) := by
    apply Real.sqrt_pos.mpr; nlinarith
  rw [brownianDensity_eq hu0, div_le_div_iff₀ (by positivity) hx4]
  have hstep : (Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-x ^ 2 / (2 * u)) * x ^ 4
      ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ * (16 * u ^ 2 / x ^ 4) * x ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hexp
      (by positivity : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * u))⁻¹)
    nlinarith [hmul]
  have hsimp : (Real.sqrt (2 * Real.pi * u))⁻¹ * (16 * u ^ 2 / x ^ 4) * x ^ 4
      = 16 * u ^ 2 / Real.sqrt (2 * Real.pi * u) := by field_simp
  rw [hsimp] at hstep
  have hfin : 16 * u ^ 2 / Real.sqrt (2 * Real.pi * u) ≤ 16 * u := by
    rw [div_le_iff₀ hspos]; nlinarith [hsqrt, hu0.le]
  linarith

/-- **The bound above the origin.** `g_u(x) ≤ 1` for `u ≥ 1`, so the mixture integrand is
dominated there by `k_I(u)/u` — the second integrability field, verbatim.
@isnad1 id=le.1h2v.s4.e6f1bee44e01 from=translated src=- shape=c89cfe8b vocab=e35bb2fa
-/
theorem brownianDensity_le_one {u : ℝ} (hu : 1 ≤ u) (x : ℝ) : brownianDensity u x ≤ 1 := by
  have hpi := Real.two_le_pi
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hspos : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * u) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt; nlinarith
  have hle : -x ^ 2 / (2 * u) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg x]
    · positivity
  have hexp : Real.exp (-x ^ 2 / (2 * u)) ≤ 1 := Real.exp_le_one_iff.mpr hle
  have hinv : (Real.sqrt (2 * Real.pi * u))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hspos
  rw [brownianDensity_eq hu0]
  nlinarith [Real.exp_pos (-x ^ 2 / (2 * u)),
    inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * u))]

/-! ## The Gaussian jump integral -/

/-- Integration against `g_u` is integration against its density.
@isnad1 id=eq.2h2v.s6.03b3a98dc146 from=translated src=- shape=857f2e5b vocab=460e022d
-/
theorem lintegral_brownianDensity {u : ℝ} (hu : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (brownianDensity u x) * g x) = ∫⁻ x, g x ∂(brownianLaw u) := by
  rw [brownianLaw_eq_withDensity hu,
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_brownianDensity u).ennreal_ofReal) hg]
  rfl

/-- An even function integrates over the line to twice its integral over the positive axis.
@isnad1 id=eq.1h1v.s6.ae214ea31845 from=translated src=- shape=27addeeb vocab=606f1621
-/
theorem lintegral_even_eq_two_mul {g : ℝ → ℝ≥0∞} (heven : ∀ x, g (-x) = g x) :
    (∫⁻ x, g x) = 2 * ∫⁻ x in Ioi (0 : ℝ), g x := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0 : ℝ)) = Iio (0 : ℝ) := by ext x; simp
  have hIio : (∫⁻ x in Iio (0 : ℝ), g x) = ∫⁻ x in Ioi (0 : ℝ), g x := by
    have hkey := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi (0 : ℝ))
    rw [hpre] at hkey
    rw [← hkey]
    exact setLIntegral_congr_fun measurableSet_Iio fun x _ => (heven x).symm
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ)) g
    (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hIci : (∫⁻ x in Ici (0 : ℝ), g x) = ∫⁻ x in Ioi (0 : ℝ), g x :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hIio, hIci] at hsplit
  rw [← hsplit]
  ring

/-! ## Mixtures against the Brownian laws -/

/-- The mixture of Gaussian laws against a probability law is a probability measure.
@isnad1 id=isprobab.0h1v.s4.da87af001ec2 from=translated src=- shape=9802d443 vocab=1578d94b
-/
theorem isProbabilityMeasure_bind_brownianLaw (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (ρ.bind brownianLaw) := by
  refine isProbabilityMeasure_bind measurable_brownianLaw.aemeasurable (.of_forall fun u => ?_)
  rw [brownianLaw]; infer_instance

end ScaleSpace
