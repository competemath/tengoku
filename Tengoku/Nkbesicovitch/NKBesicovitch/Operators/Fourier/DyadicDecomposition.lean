/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Fourier.FrequencyKernels
public import Tengoku.Seed.Analysis.Fourier.Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact finite dyadic frequency decomposition

Successive dilations of the annular difference telescope to a single dilated
low-frequency kernel. Convolution gives the corresponding finite decomposition
of a Schwartz input, with an explicit smooth Fourier cutoff.
-/

public section

open MeasureTheory Set FourierTransform
open scoped SchwartzMap FourierTransform

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Annular kernel dilations telescope exactly to the largest low-frequency dilation.
@isnad1 id=eq.0h3v.s8.6b8e2936f5a1 from=translated src=- shape=4086a5d3 vocab=061912fc
-/
theorem sum_normalizedDilation_annular (φ : 𝓢(E, ℂ)) (N : ℕ) :
    φ + ∑ j ∈ Finset.range N, normalizedDilation ((2 : ℝ) ^ j) (pow_pos two_pos j)
      (normalizedDilation 2 two_pos φ - φ) =
        normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [Finset.sum_range_succ, ← add_assoc, hN, normalizedDilation_sub,
      normalizedDilation_mul]
    simp only [← pow_succ]
    abel

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The finite dyadic decomposition of an input is convolution with one dilated cutoff kernel.
@isnad1 id=eq.0h4v.s13.3f19a61b4d50 from=translated src=- shape=5360a879 vocab=8f387bd2
-/
theorem sum_convolution_normalizedDilation_annular (φ f : 𝓢(E, ℂ)) (N : ℕ) :
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) φ f +
      ∑ j ∈ Finset.range N, SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
        (normalizedDilation ((2 : ℝ) ^ j) (pow_pos two_pos j)
          (normalizedDilation 2 two_pos φ - φ)) f =
            SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
              (normalizedDilation ((2 : ℝ) ^ N) (pow_pos two_pos N) φ) f := by
  have h := congrArg (fun ψ : 𝓢(E, ℂ) ↦
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f)
    (sum_normalizedDilation_annular φ N)
  simpa only [map_add, map_sum, add_apply, sum_apply] using h

/-- The telescoped dyadic approximation is the input Fourier transform times its smooth cutoff.
@isnad1 id=eq.1h5v.s12.96de50c55a09 from=translated src=- shape=084952c7 vocab=af30629a
-/
theorem fourier_convolution_normalizedDilation (φ f : 𝓢(E, ℂ)) (a : ℝ) (ha : 0 < a) (ξ : E) :
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation a ha φ) f) ξ = 𝓕 φ (a⁻¹ • ξ) * 𝓕 f ξ := by
  simp only [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.lsmul_apply, fourier_normalizedDilation, smul_eq_mul]

end NKBesicovitch
