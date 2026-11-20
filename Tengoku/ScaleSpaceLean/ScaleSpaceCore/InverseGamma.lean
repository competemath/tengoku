/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.Seed.MeasureTheory.Function.JacobianOneDim
import Tengoku.Seed.MeasureTheory.Integral.Gamma
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The inverse-gamma integral and the inverse-gamma law

Home: none (standard analysis in Mathlib's types: an elementary integral identity and the
inverse-gamma law it defines, with no programme vocabulary; ref: @feller2009introduction, Ch. II
§2 (2.1), p. 47)

The general identity `∫₀^∞ t^{-1-b} e^{-c/t} dt = c^{-b} Γ(b)` for `b, c > 0`, with integrability
(`inverse_gamma_integral`); the exponential change of variables `u = c e^v` in `ℝ≥0∞` form
(`lintegral_Ioi_comp_exp`) and the case `c = 1/2` of the identity computed through it
(`lintegral_Ioi_inverseGammaKernel`); and the scaled inverse-gamma law of shape `a`,
`p(u) = u^{-a-1}e^{-1/(2u)}/(2^aΓ(a))` on `(0,∞)` (`inverseGammaDensity`, `inverseGammaLaw`), a
probability law carried by the half-line (`isProbabilityMeasure_inverseGammaLaw`,
`inverseGammaLaw_Iio_zero`). It is the delay law of the causal Bessel family, whose Brownian
mixture is the Student-t law (`ScaleSpaceCore.StudentTransform`).

Moved (Q-0363, SSL-8), statements unchanged up to the namespace:
* `inverse_gamma_integral` from Paper VII (`Formalization/AffineHemigroup/Subordination.lean`);
* `inverseGammaDensity` and `inverseGammaLaw` from Paper V's cone export (`cone-v0.1`,
  `f28c066e`, `SpatialLine.Corners`); the exponential substitution (`expMap_image`,
  `expMap_monotone`, `expMap_hasDeriv`, `lintegral_Ioi_comp_exp`, `exp_rpow`) from
  `SpatialLine.FirstPassage`; `lintegral_Ioi_inverseGammaKernel`,
  `inverseGammaDensity_eq_indicator`, `inverseGammaLaw_Iio_zero` and
  `isProbabilityMeasure_inverseGammaLaw` from `SpatialLine.StudentTransform`;
  `measurable_inverseGammaDensity` and `inverseGammaDensity_nonneg` from `SpatialLine.BridgeBessel`.

Paper V's `lintegral_Ioi_inverseGammaKernel` and Paper VII's `integral_rpow_exp_inv`
(`MaternKernel`) are cases of `inverse_gamma_integral`, at `c = 1/2` and `c = 1/4`; each keeps the
proof it was written with. Everything here is proved from Mathlib alone.

## References

* @feller2009introduction, Ch. II §2 (2.1), p. 47: Euler's integral `Γ(t) = ∫₀^∞ x^{t-1} e^{-x} dx`
  — `inverse_gamma_integral` is this identity read through the reciprocal substitution `t = 1/y`.
  The inverse-gamma density and law built from it (`inverseGammaDensity`, `inverseGammaLaw`) are
  this module's own normalisation, not separately cited.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The inverse-gamma integral -/

/-! ## The exponential change of variables -/

/-- The exponential change of variables `v ↦ c e^v`, from the line onto `(0,∞)`.
@isnad1 id=eq.1h1v.s5.da36bc6acf57 from=translated src=- shape=ca7f1450 vocab=f77f418d
-/
theorem expMap_image {c : ℝ} (hc : 0 < c) :
    (fun v : ℝ => c * Real.exp v) '' univ = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨v, -, rfl⟩
    exact mul_pos hc (Real.exp_pos v)
  · intro hy
    refine ⟨Real.log (y / c), mem_univ _, ?_⟩
    show c * Real.exp (Real.log (y / c)) = y
    rw [Real.exp_log (div_pos hy hc)]
    field_simp

/--
@isnad1 id=monotone.1h1v.s5.bcd3cb64c6af from=translated src=- shape=860b29d0 vocab=aa248e07
-/
theorem expMap_monotone {c : ℝ} (hc : 0 < c) :
    MonotoneOn (fun v : ℝ => c * Real.exp v) univ := by
  intro x _ y _ hxy
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy) hc.le

/--
@isnad1 id=hasderiv.0h2v.s5.7b5e7231c811 from=translated src=- shape=3b346da5 vocab=da9d0ba9
-/
theorem expMap_hasDeriv (c v : ℝ) :
    HasDerivAt (fun w : ℝ => c * Real.exp w) (c * Real.exp v) v :=
  (Real.hasDerivAt_exp v).const_mul c

/-- The change of variables in `ℝ≥0∞` form.

It is `lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`, which asks only for measurability
of the domain, the derivative and monotonicity: no injectivity argument and no integrability side
condition.
@isnad1 id=eq.1h2v.s6.d514eabbddfd from=translated src=- shape=db0909d1 vocab=1bfeb9c9
-/
theorem lintegral_Ioi_comp_exp {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (0 : ℝ), g u)
      = ∫⁻ v, ENNReal.ofReal (c * Real.exp v) * g (c * Real.exp v) := by
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := (univ : Set ℝ)) (f := fun v : ℝ => c * Real.exp v)
    (f' := fun v : ℝ => c * Real.exp v) MeasurableSet.univ
    (fun v _ => (expMap_hasDeriv c v).hasDerivWithinAt) (expMap_monotone hc) g
  rw [expMap_image hc] at h
  rw [h, setLIntegral_univ]

/--
@isnad1 id=eq.0h2v.s4.8aeec0590dbe from=translated src=- shape=e590dbf5 vocab=97fcab74
-/
theorem exp_rpow (v y : ℝ) : (Real.exp v) ^ y = Real.exp (v * y) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]

/-! ## The mass of the inverse-gamma law -/

/-- **The mass of the inverse-gamma law.** `∫_0^∞ u^{-a-1}e^{-1/(2u)}\,du = 2^a\Gamma(a)`.

Two exponential substitutions and one reflection: `u = e^v` turns the integral into
`∫_ℝ e^{-av}e^{-e^{-v}/2}dv`, the reflection `v \mapsto -v` into `∫_ℝ e^{av}e^{-e^v/2}dv`, and
`u = e^v` read backwards into the Gamma integral at rate `1/2`. Mathlib's
`integral_rpow_mul_exp_neg_mul_Ioi` evaluates that one, and the positivity trick carries the
value back into `ℝ≥0∞`.
@isnad1 id=eq.1h1v.s6.7932370aac99 from=translated src=- shape=85eb636d vocab=36fa18ea
-/
theorem lintegral_Ioi_inverseGammaKernel {a : ℝ} (ha : 0 < a) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)))
      = ENNReal.ofReal (2 ^ a * Real.Gamma a) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  -- the two sides, each pushed onto the line
  have hleft : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (-(a * v)) * Real.exp (-(Real.exp (-v) / 2))) := by
    rw [lintegral_Ioi_comp_exp (c := 1) one_pos]
    refine lintegral_congr fun v => ?_
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_mul, exp_rpow,
      show ((2 : ℝ) * Real.exp v)⁻¹ = Real.exp (-v) / 2 from by
        rw [Real.exp_neg]; field_simp,
      ← mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hright : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u))))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (a * v) * Real.exp (-(Real.exp v / 2))) := by
    rw [lintegral_Ioi_comp_exp (c := 1) one_pos]
    refine lintegral_congr fun v => ?_
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_mul, exp_rpow,
      show -((2 : ℝ)⁻¹ * Real.exp v) = -(Real.exp v / 2) from by ring,
      ← mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hrefl : (∫⁻ v, ENNReal.ofReal (Real.exp (-(a * v)) * Real.exp (-(Real.exp (-v) / 2))))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (a * v) * Real.exp (-(Real.exp v / 2))) := by
    have hkey := hmp.lintegral_comp_emb hemb
      (fun v => ENNReal.ofReal (Real.exp (a * v) * Real.exp (-(Real.exp v / 2))))
    rw [← hkey]
    refine lintegral_congr fun v => ?_
    congr 1
    congr 1
    congr 1
    ring
  -- and the Gamma evaluation
  have hgamma : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u))))
      = ENNReal.ofReal (2 ^ a * Real.Gamma a) := by
    have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by norm_num : (0:ℝ) < 2⁻¹)
    have hpos : (0 : ℝ) < 2 ^ a * Real.Gamma a := by
      have := Real.Gamma_pos_of_pos ha
      positivity
    have hcoe : ((1 : ℝ) / 2⁻¹) ^ a * Real.Gamma a = 2 ^ a * Real.Gamma a := by
      norm_num
    rw [hcoe] at hval
    have hb : (∫ u in Ioi (0 : ℝ), u ^ (a - 1) * Real.exp (-(2⁻¹ * u)))
        = (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u)))).toReal := by
      refine integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have : (0 : ℝ) < u := hu
      positivity
    rw [hb] at hval
    set X := ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(2⁻¹ * u))) with hX
    have hXne : X ≠ ⊤ := by
      intro h
      rw [h, ENNReal.toReal_top] at hval
      linarith
    rw [← ENNReal.ofReal_toReal hXne, hval]
  rw [hleft, hrefl, ← hright, hgamma]

/-! ## The inverse-gamma law -/

/-- The mixing law of the causal Bessel family: the scaled inverse-gamma density
`p_{T_1}(u) = u^{-a-1}e^{-1/(2u)}/(2^a\Gamma(a))` on `(0,∞)`.-/
noncomputable def inverseGammaDensity (a u : ℝ) : ℝ :=
  Set.indicator (Ioi (0 : ℝ))
    (fun u => u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹) / (2 ^ a * Real.Gamma a)) u

/-- The scaled inverse-gamma law of shape `a`, the causal Bessel family's delay law.-/
noncomputable def inverseGammaLaw (a : ℝ) : Measure ℝ :=
  volume.withDensity fun u => ENNReal.ofReal (inverseGammaDensity a u)

/--
@isnad1 id=measurab.0h1v.s3.59b1e8029cc1 from=translated src=- shape=f736e2c1 vocab=40453e5f
-/
theorem measurable_inverseGammaDensity (a : ℝ) : Measurable (inverseGammaDensity a) := by
  unfold inverseGammaDensity
  refine Measurable.indicator ?_ measurableSet_Ioi
  fun_prop

/--
@isnad1 id=le.1h2v.s4.17be271bd762 from=translated src=- shape=1852429d vocab=d70eb7fa
-/
theorem inverseGammaDensity_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) :
    0 ≤ inverseGammaDensity a u := by
  unfold inverseGammaDensity
  refine Set.indicator_nonneg (fun t ht => ?_) u
  have ht0 : (0 : ℝ) < t := ht
  have h1 : (0 : ℝ) < t ^ (-a - 1) := Real.rpow_pos_of_pos ht0 _
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have h3 : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  positivity

/--
@isnad1 id=eq.0h1v.s6.a38026912588 from=translated src=- shape=b62c2fab vocab=5c599c13
-/
theorem inverseGammaDensity_eq_indicator (a : ℝ) :
    (fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u))
      = Set.indicator (Ioi (0 : ℝ))
          (fun u => ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)
            * (2 ^ a * Real.Gamma a)⁻¹)) := by
  funext u
  by_cases h : u ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, inverseGammaDensity, Set.indicator_of_mem h]
    congr 1
  · rw [Set.indicator_of_notMem h, inverseGammaDensity, Set.indicator_of_notMem h]
    simp

/-- The inverse-gamma law is carried by the half-line.
@isnad1 id=eq.0h1v.s5.24ded92c04d6 from=translated src=- shape=0b4cdb55 vocab=739256b9
-/
theorem inverseGammaLaw_Iio_zero (a : ℝ) : inverseGammaLaw a (Iio 0) = 0 := by
  rw [inverseGammaLaw, withDensity_apply _ measurableSet_Iio,
    inverseGammaDensity_eq_indicator]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => (0 : ℝ≥0∞)) ?_]
  · simp
  · intro u hu
    exact Set.indicator_of_notMem (by simpa using le_of_lt hu) _

/-- The inverse-gamma law of positive shape is a probability law.
@isnad1 id=isprobab.1h1v.s4.f2aa01bb1261 from=translated src=- shape=b8038e13 vocab=eb48520f
-/
theorem isProbabilityMeasure_inverseGammaLaw {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (inverseGammaLaw a) := by
  have hpos : (0 : ℝ) < 2 ^ a * Real.Gamma a := by
    have := Real.Gamma_pos_of_pos ha
    positivity
  constructor
  rw [inverseGammaLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    inverseGammaDensity_eq_indicator, lintegral_indicator measurableSet_Ioi]
  have hstep : ∀ u : ℝ, ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)
        * (2 ^ a * Real.Gamma a)⁻¹)
      = ENNReal.ofReal ((2 ^ a * Real.Gamma a)⁻¹)
        * ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)) := by
    intro u
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp only [hstep]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioi_inverseGammaKernel ha,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]

end ScaleSpace
