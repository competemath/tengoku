/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Fourier.Plancherel
public import Tengoku.Seed.Analysis.Fourier.Convolution
public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two-norm bound for a Schwartz convolution multiplier

Plancherel bounds convolution on `L²` by the uniform norm of the Fourier
transform of its kernel. This bound does not require bounded spatial support.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=le.1h4v.s12.d8cc981baaef from=translated src=- shape=38bda9a8 vocab=64b64345
-/
theorem eLpNorm_schwartz_convolution_two_le (f ψ : 𝓢(E, ℂ)) (B : ℝ≥0)
    (hB : ∀ ξ, ‖𝓕 ψ ξ‖ₑ ≤ B) :
    eLpNorm (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) 2 volume ≤
      B * eLpNorm f 2 volume := by
  rw [← eLpNorm_fourier_two (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f),
    ← eLpNorm_fourier_two f]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  apply ae_of_all
  intro ξ
  simp only [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.lsmul_apply, enorm_smul]
  exact mul_le_mul' (hB ξ) le_rfl

end NKBesicovitch
