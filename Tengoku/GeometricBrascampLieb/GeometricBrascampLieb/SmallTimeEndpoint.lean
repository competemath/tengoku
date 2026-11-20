import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.HeatScaling
import Tengoku.Seed.Analysis.Real.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Recovery of bounded continuous initial data at small heat times -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussianConvolution_swap (f : E → ℝ) (b : ℝ) (x : E) :
    gaussianConvolution b f x = ∫ z, f (x-z)*Real.exp (-b*‖z‖^2) := by
  change (f ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun z : E => Real.exp (-b*‖z‖^2))) x = _
  exact convolution_mul_swap

/-- A fixed Gaussian kernel, with the small spatial scale moved into the input.-/
theorem heatConvolution_sq_eq_integral (f : E → ℝ) {a : ℝ} (ha : 0 < a) (x : E) :
    heatConvolution f (a^2) x =
      ∫ z, (heatNormalization (E := E) 1*Real.exp (-(1/4 : ℝ)*‖z‖^2))*f (x-a • z) := by
  let G := fun z : E => f (x-z)*Real.exp (-(4*a^2)⁻¹*‖z‖^2)
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure E) G a (hR := ha.le)
  rw [smul_eq_mul] at hs
  rw [heatConvolution, gaussianConvolution_swap, heatNormalization_scale ha, exp_neg_nat_mul_log ha]
  calc
    _ = heatNormalization (E := E) 1*(∫ z, G (a • z)) := by rw [hs]; ring
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        have he := gaussian_exponent_scale ha z (0 : E)
        simp only [sub_zero, smul_zero] at he
        change heatNormalization (E := E) 1*(f (x-a • z)*Real.exp (-(4*a^2)⁻¹*‖a • z‖^2)) = _
        rw [he]
        ring

theorem initialAverage_continuousAt_zero {f : E → ℝ} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) (x : E) :
    ContinuousAt (fun a : ℝ =>
      ∫ z, (heatNormalization (E := E) 1*Real.exp (-(1/4 : ℝ)*‖z‖^2))*f (x-a • z)) 0 := by
  let k := fun z : E => heatNormalization (E := E) 1*Real.exp (-(1/4 : ℝ)*‖z‖^2)
  have hk : ∀ z, 0 < k z := fun z => mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  apply continuousAt_of_dominated (bound := fun z => C*k z)
  · exact Eventually.of_forall fun a => (hkc.mul (hf.comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall fun a => Eventually.of_forall fun z => by
      change ‖k z*f (x-a • z)‖ ≤ C*k z
      rw [norm_mul, Real.norm_eq_abs (k z), abs_of_pos (hk z)]
      exact (mul_le_mul_of_nonneg_left (hbound _) (hk z).le).trans_eq (mul_comm _ _)
  · exact ((integrable_gaussian (E := E) (by norm_num : 0 < (1/4 : ℝ))).const_mul _).const_mul C
  · exact Eventually.of_forall fun z => by
      change ContinuousAt (fun a : ℝ => k z*f (x-a • z)) 0
      exact continuous_const.continuousAt.mul (hf.continuousAt.comp (by fun_prop))

/-- Small-time convergence, first in the square-root time parameter.-/
theorem heatConvolution_tendsto_sq_zero {f : E → ℝ} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) (x : E) :
    Tendsto (fun a : ℝ => heatConvolution f (a^2) x) (𝓝[>] 0) (𝓝 (f x)) := by
  have h := (initialAverage_continuousAt_zero hf hbound x).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [zero_smul, sub_zero, integral_mul_const, integral_normalized_gaussian, one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  exact (heatConvolution_sq_eq_integral f ha x).symm

/-- Positive-time heat regularization tends to the bounded continuous input.-/
theorem heatConvolution_tendsto_zero {f : E → ℝ} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) (x : E) :
    Tendsto (fun t => heatConvolution f t x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact Real.sqrt_pos.mpr ht
  have h := (heatConvolution_tendsto_sq_zero hf hbound x).comp hsqrt
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  change heatConvolution f ((Real.sqrt t)^2) x = _
  rw [Real.sq_sqrt ht.le]

end GeometricBrascampLieb
