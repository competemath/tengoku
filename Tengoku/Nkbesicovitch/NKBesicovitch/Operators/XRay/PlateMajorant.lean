/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.FrameContinuity
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.Bandlimited
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateContinuousFamily
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Fourier.BandlimitedPlane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable plate majorants for signed X-ray integrals

Bandlimited X-ray fibers admit full-plane bounds by their polynomially
weighted plate maxima. These majorants are jointly Borel in the frame
and the lower-dimensional plane, so their frequency sums can be integrated.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Full-plane integrals of bandlimited signed X-ray fibers have uniform plate majorants.
@isnad1 id=ex.2h7v.s14.4f42a03f031f from=translated src=- shape=227c3ce7 vocab=bfd3a0c0
-/
theorem exists_lintegral_frameLineIntegral_le_plateMaximal {A : ℕ} (hA : k < 2 * A)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0, ∀ (a : ℝ), 0 < a → ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      tsupport (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ⊆ closedBall 0 (a * R) →
        ∀ (u : Rotations n) (V : Grassmannian m k) (x : EuclideanSpace ℝ (Fin m)),
          (∫⁻ w : V.val, ‖frameLineIntegral v b f u (x + w)‖ₑ) ≤
            C * plateMaximal a⁻¹
              (fun y ↦ ‖(1 + ‖y‖ ^ 2) ^ A • frameLineIntegral v b f u y‖ₑ) V := by
  obtain ⟨C, hC⟩ := exists_lintegral_plane_le_plateMaximal_of_bandlimited hA R hR
  refine ⟨C, fun a ha f hf u V x ↦ ?_⟩
  obtain ⟨g, hg, hs⟩ := exists_weighted_schwartz_frameLineIntegral_bandlimited v b f hf u 0
  simpa only [hg, pow_zero, one_smul] using hC a ha g hs V x

end NKBesicovitch.XRay
