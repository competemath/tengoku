/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.RegularizedTartar
import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Fourier
public import Tengoku

/-!
# Tartar Derivative Bounds

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A tartar amplitude derivative integrand used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeDerivativeIntegrand (x t : ℝ) : ℝ :=
  -t * Tartar.weight t * Real.sin (x * t)

/--
@isnad1 id=hasderiv.0h2v.s5.1bb6288c5f5e from=translated src=- shape=3c5d6a1b vocab=7c0c6f3b
-/
theorem hasDerivAt_tartarWeight_mul_cos (x t : ℝ) :
    HasDerivAt (fun z : ℝ ↦ Tartar.weight t * Real.cos (z * t))
      (tartarAmplitudeDerivativeIntegrand x t) x := by
  unfold tartarAmplitudeDerivativeIntegrand
  have hcos :=
    ((hasDerivAt_id x).mul_const t).cos.const_mul (Tartar.weight t)
  grind

/--
@isnad1 id=integrab.0h0v.s5.858060702d76 from=translated src=- shape=15793ce9 vocab=45b512ef
-/
theorem abs_mul_tartarWeight_integrable :
    Integrable (fun t : ℝ ↦ |t| * Tartar.weight t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_abs.mul tartarWeight_continuous
  · exact tartarWeight_hasCompactSupport.mul_left

/--
@isnad1 id=le.0h2v.s4.d1ab45ddb274 from=translated src=- shape=23731155 vocab=c1d5527f
-/
theorem norm_tartarAmplitudeDerivativeIntegrand_le (x t : ℝ) :
    ‖tartarAmplitudeDerivativeIntegrand x t‖ ≤
      |t| * Tartar.weight t := by
  rw [tartarAmplitudeDerivativeIntegrand, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (tartarWeight_nonneg t)]
  calc
    |t| * Tartar.weight t * |Real.sin (x * t)| ≤
        |t| * Tartar.weight t * 1 := by
      exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
        (mul_nonneg (abs_nonneg _) (tartarWeight_nonneg t))
    _ = _ := mul_one _

/--
@isnad1 id=hasderiv.0h1v.s6.2c76bf0913a3 from=translated src=- shape=3971f0ef vocab=a307a7aa
-/
theorem hasDerivAt_integral_tartarWeight_mul_cos (x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∫ t : ℝ,
        Tartar.weight t * Real.cos (z * t))
      (∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t) x := by
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (x₀ := x) (s := Set.univ)
      (F := fun z t : ℝ ↦ Tartar.weight t * Real.cos (z * t))
      (F' := tartarAmplitudeDerivativeIntegrand)
      (bound := fun t : ℝ ↦ |t| * Tartar.weight t)
      univ_mem
      (by
        filter_upwards [] with z
        exact (tartarWeight_continuous.mul
          (by fun_prop : Continuous (fun t : ℝ ↦ Real.cos (z * t))))
          |>.aestronglyMeasurable)
      (tartarWeight_mul_cos_integrable x)
      (by
        have hc : Continuous
            (tartarAmplitudeDerivativeIntegrand x) := by
          unfold tartarAmplitudeDerivativeIntegrand
          exact (continuous_id.neg.mul tartarWeight_continuous).mul
            (Real.continuous_sin.comp
              (continuous_const.mul continuous_id))
        exact hc.aestronglyMeasurable)
      (by
        filter_upwards [] with t z _
        exact norm_tartarAmplitudeDerivativeIntegrand_le z t)
      abs_mul_tartarWeight_integrable
      (by
        filter_upwards [] with t z _
        exact hasDerivAt_tartarWeight_mul_cos z t)
  simp_all

/--
@isnad1 id=hasderiv.0h1v.s6.b8c5bf5db8c1 from=translated src=- shape=dce617e4 vocab=32755086
-/
theorem hasDerivAt_tartarAmplitude (x : ℝ) :
    HasDerivAt Tartar.amplitude
      ((3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t) x := by
  have h :=
    (hasDerivAt_integral_tartarWeight_mul_cos x).const_mul (3 / 4 : ℝ)
  have heq :
      Tartar.amplitude =
        fun z : ℝ ↦ (3 / 4 : ℝ) *
          ∫ t : ℝ, Tartar.weight t * Real.cos (z * t) := by
    funext z
    exact tartarAmplitude_eq_cosineTransform z
  simp_all

/--
@isnad1 id=differen.0h0v.s5.e57fc31df987 from=translated src=- shape=aa9fb30a vocab=d45ad8d3
-/
theorem differentiable_tartarAmplitude :
    Differentiable ℝ Tartar.amplitude :=
  fun x ↦ (hasDerivAt_tartarAmplitude x).differentiableAt

/--
@isnad1 id=continuo.0h0v.s5.0ff18a0f53f4 from=translated src=- shape=c4c93567 vocab=505b38c1
-/
theorem continuous_integral_tartarAmplitudeDerivativeIntegrand :
    Continuous
      (fun x : ℝ ↦
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto
    (fun z : ℝ ↦ ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand z t)
    (𝓝 x)
    (𝓝 (∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t))
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ ↦ |t| * Tartar.weight t)
  · filter_upwards [] with z
    have hc : Continuous
        (tartarAmplitudeDerivativeIntegrand z) := by
      unfold tartarAmplitudeDerivativeIntegrand
      exact (continuous_id.neg.mul tartarWeight_continuous).mul
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_id))
    exact hc.aestronglyMeasurable
  · filter_upwards [] with z
    filter_upwards [] with t
    exact norm_tartarAmplitudeDerivativeIntegrand_le z t
  · exact abs_mul_tartarWeight_integrable
  · filter_upwards [] with t
    unfold tartarAmplitudeDerivativeIntegrand
    exact (by fun_prop : Continuous
      (fun z : ℝ ↦ -t * Tartar.weight t * Real.sin (z * t))).continuousAt

/--
@isnad1 id=eq.0h1v.s6.05b3076c6f22 from=translated src=- shape=6e7b049b vocab=c4554ad8
-/
theorem deriv_tartarAmplitude (x : ℝ) :
    deriv Tartar.amplitude x =
      (3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t :=
  (hasDerivAt_tartarAmplitude x).deriv

/--
@isnad1 id=continuo.0h0v.s5.6b851251d465 from=translated src=- shape=d252d346 vocab=5ee4d069
-/
theorem continuous_deriv_tartarAmplitude :
    Continuous (deriv Tartar.amplitude) := by
  rw [show deriv Tartar.amplitude =
      fun x : ℝ ↦ (3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand x t by
    funext x
    exact deriv_tartarAmplitude x]
  exact continuous_const.mul
    continuous_integral_tartarAmplitudeDerivativeIntegrand

end NumberField.Odlyzko

end

section

open MeasureTheory Real

namespace NumberField.Odlyzko

/-- A tartar amplitude derivative bound used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeDerivativeBound : ℝ :=
  (3 / 4 : ℝ) * ∫ t : ℝ, |t| * Tartar.weight t

/--
@isnad1 id=le.0h0v.s3.f572115abdaf from=translated src=- shape=ff3a10fc vocab=e20692d2
-/
theorem tartarAmplitudeDerivativeBound_nonneg :
    0 ≤ tartarAmplitudeDerivativeBound := by
  unfold tartarAmplitudeDerivativeBound
  exact mul_nonneg (by norm_num) (integral_nonneg fun t ↦
    mul_nonneg (abs_nonneg t) (tartarWeight_nonneg t))

/--
@isnad1 id=le.0h1v.s5.b7e4003c5b1e from=translated src=- shape=6bd8b21c vocab=f99eacc8
-/
theorem abs_deriv_tartarAmplitude_le (x : ℝ) :
    |deriv Tartar.amplitude x| ≤ tartarAmplitudeDerivativeBound := by
  rw [deriv_tartarAmplitude, tartarAmplitudeDerivativeBound, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  gcongr
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le abs_mul_tartarWeight_integrable
    (.of_forall fun t ↦ norm_tartarAmplitudeDerivativeIntegrand_le x t)

/--
@isnad1 id=hasderiv.0h1v.s6.518a9b7f282d from=translated src=- shape=21a16dd9 vocab=9094fe6b
-/
theorem hasDerivAt_tartarTestFunction (x : ℝ) :
    HasDerivAt Tartar.testFunction
      (2 * Tartar.amplitude x * deriv Tartar.amplitude x) x := by
  change HasDerivAt (fun z ↦ Tartar.amplitude z ^ 2)
    (2 * Tartar.amplitude x * deriv Tartar.amplitude x) x
  have h := (hasDerivAt_tartarAmplitude x).mul
    (hasDerivAt_tartarAmplitude x)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by
    simp only [Pi.mul_apply, pow_two])).congr_deriv ?_
  rw [deriv_tartarAmplitude]
  ring

/--
@isnad1 id=eq.0h1v.s6.38665c3a4146 from=translated src=- shape=d13a2750 vocab=815c9936
-/
theorem deriv_tartarTestFunction (x : ℝ) :
    deriv Tartar.testFunction x =
      2 * Tartar.amplitude x * deriv Tartar.amplitude x :=
  (hasDerivAt_tartarTestFunction x).deriv

/--
@isnad1 id=le.0h1v.s5.0d3f787d370b from=translated src=- shape=bbd4a667 vocab=7f49410f
-/
theorem abs_deriv_tartarTestFunction_le (x : ℝ) :
    |deriv Tartar.testFunction x| ≤
      2 * tartarAmplitudeDerivativeBound := by
  rw [deriv_tartarTestFunction, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |Tartar.amplitude x| * |deriv Tartar.amplitude x| ≤
        2 * 1 * tartarAmplitudeDerivativeBound := by
      gcongr
      · exact abs_tartarAmplitude_le_one x
      · exact abs_deriv_tartarAmplitude_le x
    _ = _ := by ring

/--
@isnad1 id=hasderiv.0h2v.s6.324455ced961 from=translated src=- shape=3eae6507 vocab=d650356e
-/
theorem hasDerivAt_scaledTartarTestFunction (y x : ℝ) :
    HasDerivAt (scaledTartarTestFunction y)
      (y * deriv Tartar.testFunction (y * x)) x := by
  unfold scaledTartarTestFunction
  have h := (hasDerivAt_tartarTestFunction (y * x)).comp x
    ((hasDerivAt_id x).const_mul y)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦
    rfl)).congr_deriv ?_
  rw [deriv_tartarTestFunction]
  ring

/-- A regularized scaled tartar derivative used in the Odlyzko-bound argument. -/
noncomputable def regularizedScaledTartarDerivative
    (y δ x : ℝ) : ℝ :=
  (y * deriv Tartar.testFunction (y * x) -
      2 * δ * x * scaledTartarTestFunction y x) *
    Real.exp (-δ * x ^ 2)

/--
@isnad1 id=hasderiv.0h3v.s5.56f128bad65c from=translated src=- shape=fef50917 vocab=c842d4cf
-/
theorem hasDerivAt_regularizedScaledTartar (y δ x : ℝ) :
    HasDerivAt (regularizedScaledTartar y δ)
      (regularizedScaledTartarDerivative y δ x) x := by
  unfold regularizedScaledTartar regularizedScaledTartarDerivative
  have hgauss :
      HasDerivAt (fun z : ℝ ↦ Real.exp (-δ * z ^ 2))
        (-2 * δ * x * Real.exp (-δ * x ^ 2)) x := by
    have h := (((hasDerivAt_id x).pow 2).const_mul (-δ)).exp
    convert h using 1 <;>
      simp only [Pi.pow_apply, id_eq]
    ring
  have hprod :=
    (hasDerivAt_scaledTartarTestFunction y x).mul hgauss
  exact hprod.congr_deriv (by ring)

/--
@isnad1 id=continuo.0h2v.s4.4c011e90e041 from=translated src=- shape=443e0365 vocab=86ec1093
-/
theorem continuous_regularizedScaledTartarDerivative (y δ : ℝ) :
    Continuous (regularizedScaledTartarDerivative y δ) := by
  have hderivTest : Continuous (deriv Tartar.testFunction) := by
    rw [show deriv Tartar.testFunction = fun x ↦
        2 * Tartar.amplitude x * deriv Tartar.amplitude x by
      funext x
      exact deriv_tartarTestFunction x]
    exact (continuous_const.mul differentiable_tartarAmplitude.continuous).mul
      continuous_deriv_tartarAmplitude
  have hscaled : Continuous (scaledTartarTestFunction y) := by
    unfold scaledTartarTestFunction
    exact tartarTestFunction_continuous.comp
      (continuous_const.mul continuous_id)
  unfold regularizedScaledTartarDerivative
  exact ((continuous_const.mul
    (hderivTest.comp (continuous_const.mul continuous_id))).sub
      ((continuous_const.mul continuous_id).mul hscaled)).mul
        (by fun_prop : Continuous
          (fun x : ℝ ↦ Real.exp (-δ * x ^ 2)))

/--
@isnad1 id=le.1h3v.s7.f7b61468798b from=translated src=- shape=652fcea2 vocab=bfbf8f12
-/
theorem abs_regularizedScaledTartarDerivative_le
    {δ : ℝ} (hδ : 0 ≤ δ) (y x : ℝ) :
    |regularizedScaledTartarDerivative y δ x| ≤
      (2 * |y| * tartarAmplitudeDerivativeBound + 2 * δ * |x|) *
        Real.exp (-δ * x ^ 2) := by
  unfold regularizedScaledTartarDerivative
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |y * deriv Tartar.testFunction (y * x) -
        2 * δ * x * scaledTartarTestFunction y x| *
          Real.exp (-δ * x ^ 2) ≤
      (|y * deriv Tartar.testFunction (y * x)| +
        |2 * δ * x * scaledTartarTestFunction y x|) *
          Real.exp (-δ * x ^ 2) := by
      gcongr
      grind
    _ ≤ (2 * |y| * tartarAmplitudeDerivativeBound + 2 * δ * |x|) *
          Real.exp (-δ * x ^ 2) := by
      gcongr
      · rw [abs_mul]
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left
            (abs_deriv_tartarTestFunction_le (y * x)) (abs_nonneg y)
      · rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hδ,
          abs_of_nonneg (scaledTartarTestFunction_nonneg y x)]
        have hcoef : 0 ≤ 2 * δ * |x| :=
          mul_nonneg (mul_nonneg (by norm_num) hδ) (abs_nonneg x)
        change 2 * δ * |x| * Tartar.testFunction (y * x) ≤
          2 * δ * |x|
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (tartarTestFunction_le_one (y * x)) hcoef

end NumberField.Odlyzko

end
