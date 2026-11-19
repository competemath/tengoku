/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.ConvolutionBound
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.AveragedFourier
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Fourier.Convolution
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Fourier.Dilation
public import Tengoku.Seed.MeasureTheory.Measure.OpenPos

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Endpoint bounds for the smoothed X-ray transform

For input supported in a fixed ball, the smoothed signed X-ray transform
has a joint infinity-norm bound controlled by the input infinity norm and
the kernel one-norm. Consequently kernels with uniformly bounded one-norm
give an endpoint bound independent of their frequency scale.
The two-norm endpoint gains half a derivative when the Fourier transform
of the smoothing kernel vanishes near zero and is uniformly bounded.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

private theorem enorm_le_eLpNorm_top {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Continuous f) (x : EuclideanSpace ℝ (Fin n)) : ‖f x‖ₑ ≤ eLpNorm f ∞ volume := by
  have hc : IsClosed {x | ‖f x‖ₑ ≤ eLpNormEssSup f volume} :=
    isClosed_le hf.enorm continuous_const
  have hd := Measure.dense_of_ae (μ := volume) (ae_le_eLpNormEssSup (f := f))
  simpa only [hc.closure_eq, mem_ofPred_eq, eLpNorm_exponent_top] using hd x

/-- A pointwise bound uniform over all rotated lines.
@isnad1 id=le.1h9v.s14.671bb772b42f from=translated src=- shape=5479197b vocab=a973d15e
-/
theorem enorm_frameLineIntegral_convolution_le
    (f ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {R : ℝ}
    (hs : Function.support (f : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ closedBall 0 R)
    (u : Rotations n) (x : EuclideanSpace ℝ (Fin m)) :
    ‖frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) u x‖ₑ ≤
      ENNReal.ofReal (2 * R) * eLpNorm f ∞ volume * eLpNorm ψ 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp only [frameLineIntegral, normalCoordinatesWithBasis_apply, map_add, map_smul,
    SchwartzMap.convolution_apply]
  apply enorm_line_convolution_le f.continuous.measurable ψ.continuous.measurable hs
    (enorm_le_eLpNorm_top f.continuous)
  exact (Unitary.linearIsometryEquiv u).norm_map (v : EuclideanSpace ℝ (Fin n)) |>.trans
    (norm_eq_of_mem_sphere v)

/-- A pointwise real bound for applying the bounded-input interpolation endpoint.
@isnad1 id=le.3h10v.s14.9b74c7b5fced from=translated src=- shape=9c4d3168 vocab=b91a4e0a
-/
theorem norm_frameLineIntegral_convolution_le_of_bound
    (f ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {R : ℝ≥0}
    (hs : Function.support (f : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ closedBall 0 R)
    {r : ℝ} (hr : 0 ≤ r) (hf : ∀ x, ‖f x‖ ≤ r) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) u x‖ ≤
      (2 * (R : ℝ) * (eLpNorm ψ 1 volume).toReal) * r := by
  have hsup : eLpNorm f ∞ volume ≤ ENNReal.ofReal r := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ hf)
  have h := (enorm_frameLineIntegral_convolution_le v b f ψ hs u x).trans
    (mul_le_mul' (mul_le_mul' le_rfl hsup) le_rfl)
  rw [← ENNReal.ofReal_toReal (ψ.memLp 1 volume).2.ne,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (R : ℝ)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (R : ℝ) * r), ← ofReal_norm] at h
  have hn := (ENNReal.ofReal_le_ofReal_iff
    (by positivity : 0 ≤ 2 * (R : ℝ) * r * (eLpNorm ψ 1 volume).toReal)).mp h
  convert hn using 1
  ring

variable [Nonempty (Fin m)]
  (w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (c : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (w : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

end NKBesicovitch.XRay
