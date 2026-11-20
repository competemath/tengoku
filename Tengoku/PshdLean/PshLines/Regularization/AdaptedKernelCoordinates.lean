import Tengoku.PshdLean.PshLines.FirstPass.ComplexManifold
import Tengoku.Seed.MeasureTheory.Measure.Haar.NormedSpace
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates adapted to finite-dimensional complex normed spaces

A finite-dimensional real normed space carrying a compatible complex vector
space structure is finite-dimensional over `ℂ`.  Consequently it admits a
continuous complex-linear equivalence with the standard complex model of its
complex dimension.  Pushing an additive Haar measure through this equivalence
gives an additive Haar measure in the coordinates, and the coordinate map is
measure-preserving for that pushed-forward measure.
-/

noncomputable section

open MeasureTheory

namespace PshLines.Regularization

open FirstPass

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E]

/-- Finite-dimensionality over `ℝ` implies finite-dimensionality over `ℂ`
when the two scalar actions form the expected tower.
@isnad1 id=finitedi.0h1v.s7.0feda4859a7c from=translated src=- shape=713b7e78 vocab=ed10e348
-/
theorem finiteDimensional_complex_of_real : FiniteDimensional ℂ E :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ E

/-- A compatible finite-dimensional complex normed space is continuously
complex-linearly equivalent to the standard complex model of the same complex
dimension.-/
noncomputable def adaptedComplexModelEquiv :
    E ≃L[ℂ] ComplexModel (Module.finrank ℂ E) := by
  letI : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  exact ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_euclideanSpace_fin])

section Measure

variable [MeasurableSpace E] [BorelSpace E]

/-- The additive Haar measure in the adapted complex coordinates.-/
noncomputable def adaptedCoordinateMeasure (μ : Measure E) :
    Measure (ComplexModel (Module.finrank ℂ E)) :=
  μ.map adaptedComplexModelEquiv

/-- Pushing an additive Haar measure through the adapted complex-linear
equivalence again gives an additive Haar measure.
@isnad1 id=isaddhaa.0h2v.s9.e98ba2e84e51 from=translated src=- shape=c999dfdb vocab=95733742
-/
theorem adaptedCoordinateMeasure_isAddHaarMeasure
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (adaptedCoordinateMeasure μ).IsAddHaarMeasure := by
  let _ : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  dsimp only [adaptedCoordinateMeasure]
  infer_instance

/-- The adapted coordinate equivalence preserves `μ` when its target is
equipped with the pushed-forward coordinate measure.
@isnad1 id=measurep.0h2v.s10.7f1718104310 from=translated src=- shape=82b219e2 vocab=6ca4b3cd
-/
theorem adaptedComplexModelEquiv_measurePreserving (μ : Measure E) :
    MeasurePreserving adaptedComplexModelEquiv μ
      (adaptedCoordinateMeasure μ) := by
  exact adaptedComplexModelEquiv.continuous.measurable.measurePreserving μ

/-- The inverse adapted coordinate equivalence preserves the coordinate
measure back to the original measure.
@isnad1 id=measurep.0h2v.s11.6e4a8e1e7b47 from=translated src=- shape=7b80dc69 vocab=b1a21fe3
-/
theorem adaptedComplexModelEquiv_symm_measurePreserving (μ : Measure E) :
    MeasurePreserving adaptedComplexModelEquiv.symm
      (adaptedCoordinateMeasure μ) μ := by
  exact MeasurePreserving.symm
    adaptedComplexModelEquiv.toHomeomorph.toMeasurableEquiv
    (adaptedComplexModelEquiv_measurePreserving μ)

/-- Change of variables from the original space to its adapted complex
coordinates.
@isnad1 id=eq.0h3v.s10.4506ee6877d1 from=translated src=- shape=72e3445d vocab=9f805ace
-/
theorem integral_comp_adaptedComplexModelEquiv (μ : Measure E)
    (f : ComplexModel (Module.finrank ℂ E) → ℝ) :
    (∫ x, f (adaptedComplexModelEquiv x) ∂μ) =
      ∫ y, f y ∂adaptedCoordinateMeasure μ := by
  exact (adaptedComplexModelEquiv_measurePreserving μ).integral_comp'
    (f := adaptedComplexModelEquiv.toHomeomorph.toMeasurableEquiv) f

end Measure

end PshLines.Regularization
