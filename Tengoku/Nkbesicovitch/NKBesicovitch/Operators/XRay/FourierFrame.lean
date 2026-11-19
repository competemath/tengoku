/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.SchwartzLine
public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.SphereRotations
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Fourier.Plancherel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Signed X-ray integrals in a fixed orthogonal frame

Ambient rotation and an orthonormal basis identify all displacement fibers
with one Euclidean space. Signed integration preserves the Schwartz class,
and the frame Fourier transform is the ambient transform on the rotated
normal hyperplane. This formulation permits integration over Haar rotations.
-/

@[expose] public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap FourierTransform ENNReal

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- The signed arclength integral in a rotated orthonormal frame.-/
noncomputable def frameLineIntegral (f : EuclideanSpace ℝ (Fin n) → ℂ) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) : ℂ :=
  ∫ t : ℝ, f (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))

/--
@isnad1 id=integrab.0h7v.s16.524b34d92dce from=translated src=- shape=0f6b1df3 vocab=d8df8124
-/
theorem integrable_frameLineIntegrand (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun t : ℝ ↦ f (Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))) := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Unitary.linearIsometryEquiv u).toContinuousLinearEquiv f
  simpa only [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    LinearIsometryEquiv.coe_coe, normalCoordinatesWithBasis_apply] using
      integrable_schwartz_normalLine (norm_eq_of_mem_sphere v) F (b x)

/-- Signed line integration is a complex linear map on the Schwartz domain.-/
noncomputable def frameLineIntegralLinearMap :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] (Rotations n × EuclideanSpace ℝ (Fin m) → ℂ) where
  toFun f z := frameLineIntegral v b f z.1 z.2
  map_add' f g := by
    funext z
    simp only [frameLineIntegral, add_apply, Pi.add_apply]
    exact integral_add (integrable_frameLineIntegrand v b f z.1 z.2)
      (integrable_frameLineIntegrand v b g z.1 z.2)
  map_smul' a f := by
    funext z
    simp only [frameLineIntegral, smul_apply, Pi.smul_apply, RingHom.id_apply, integral_smul]

/--
@isnad1 id=eq.0h5v.s15.59643c78636c from=translated src=- shape=8a311d55 vocab=6cdee941
-/
@[simp] theorem frameLineIntegralLinearMap_apply (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    frameLineIntegralLinearMap v b f =
      fun z : Rotations n × EuclideanSpace ℝ (Fin m) ↦ frameLineIntegral v b f z.1 z.2 := rfl

/--
@isnad1 id=measurab.1h5v.s14.b61c73a23c12 from=translated src=- shape=69e997ac vocab=07cf7454
-/
theorem measurable_frameLineIntegral {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Measurable f) :
    Measurable (fun z : Rotations n × EuclideanSpace ℝ (Fin m) ↦
      frameLineIntegral v b f z.1 z.2) := by
  have hm : Measurable (fun z : (Rotations n × EuclideanSpace ℝ (Fin m)) × ℝ ↦
      f (Unitary.linearIsometryEquiv z.1.1
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (z.1.2, z.2)))) :=
    hf.comp ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).clm_apply
      ((normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/--
@isnad1 id=eq.1h7v.s16.296d3fbb1a1d from=translated src=- shape=300d681f vocab=1c7886cd
-/
theorem fourier_frameLineIntegral {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f)
    (u : Rotations n) (ξ : EuclideanSpace ℝ (Fin m)) :
    𝓕 (frameLineIntegral v b f u) ξ =
      𝓕 f (Unitary.linearIsometryEquiv u (b ξ : EuclideanSpace ℝ (Fin n))) := by
  have hi : Integrable (f ∘ Unitary.linearIsometryEquiv u) :=
    (Unitary.linearIsometryEquiv u).measurePreserving.integrable_comp_of_integrable hf
  have he : frameLineIntegral v b f u =
      (fun y : (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ ↦
        ∫ t : ℝ, (f ∘ Unitary.linearIsometryEquiv u)
          ((y : EuclideanSpace ℝ (Fin n)) + t • (v : EuclideanSpace ℝ (Fin n)))) ∘ b := by
    funext x
    simp only [frameLineIntegral, normalCoordinatesWithBasis_apply, Function.comp_apply]
  rw [he, Real.fourier_comp_linearIsometry, fourier_lineIntegral (norm_eq_of_mem_sphere v) hi,
    Real.fourier_comp_linearIsometry]

/--
@isnad1 id=ex.0h6v.s12.cc5b32c185f5 from=translated src=- shape=1a2a240d vocab=50b189db
-/
theorem exists_schwartz_frameLineIntegral (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin m), ℂ), ∀ x, g x = frameLineIntegral v b f u x := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Unitary.linearIsometryEquiv u).toContinuousLinearEquiv f
  obtain ⟨g, hg⟩ := exists_schwartz_lineIntegral (norm_eq_of_mem_sphere v) F
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b.toContinuousLinearEquiv g, ?_⟩
  intro x
  simpa only [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    LinearIsometryEquiv.coe_coe, frameLineIntegral, normalCoordinatesWithBasis_apply] using hg (b x)

/--
@isnad1 id=eq.0h6v.s16.0456abe8b0ce from=translated src=- shape=a97576e6 vocab=a0f7d467
-/
theorem lintegral_enorm_sq_frameLineIntegral (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) :
    (∫⁻ x, ‖frameLineIntegral v b f u x‖ₑ ^ 2) =
      ∫⁻ ξ, ‖𝓕 f (Unitary.linearIsometryEquiv u (b ξ : EuclideanSpace ℝ (Fin n)))‖ₑ ^ 2 := by
  obtain ⟨g, hg⟩ := exists_schwartz_frameLineIntegral v b f u
  have he : (g : EuclideanSpace ℝ (Fin m) → ℂ) = frameLineIntegral v b f u := funext hg
  simpa only [SchwartzMap.fourier_coe, he, fourier_frameLineIntegral v b f.integrable]
    using (lintegral_enorm_sq_fourier g).symm

end NKBesicovitch.XRay
