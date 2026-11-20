/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Analysis.Fourier.FourierTransform
import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/--
@isnad1 id=eq.0h4v.s12.1e6e327f76e5 from=translated src=- shape=aa41432d vocab=d6f29eac
-/
theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (f ∘ A) w =
      |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ •
        𝓕 f ((A.symm : V →ₗ[ℝ] V).adjoint w) := by
  let c : ENNReal := ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹|
  have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 :=
    A.isUnit_det'.ne_zero
  have hmap : Measure.map (A : V →ₗ[ℝ] V) volume = c • volume := by
    simpa [c] using
      (MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet)
  let g : V → ℂ := fun u ↦
    𝐞 (-⟪u, (A.symm : V →ₗ[ℝ] V).adjoint w⟫) • f u
  have hgA : ∀ v : V,
      g (A v) = 𝐞 (-⟪v, w⟫) • (f ∘ A) v := by
    intro v
    have hinner :
        inner ℝ (A v) ((A.symm : V →ₗ[ℝ] V).adjoint w) = inner ℝ v w := by
      rw [LinearMap.adjoint_inner_right]
      simp
    simp only [g, Function.comp_apply, hinner]
  have hchange :
      ∫ u, g u ∂(c • volume) = ∫ v, g (A v) := by
    rw [← hmap]
    exact integral_map_equiv
      A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv g
  rw [Real.fourier_eq, Real.fourier_eq]
  simp_rw [← hgA]
  rw [← hchange, integral_smul_measure]
  simp only [c, ENNReal.toReal_ofReal, abs_nonneg, g]
  rw [abs_inv]

end SRG266.Lattice
