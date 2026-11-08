module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ResidualScalar
public import Tengoku.Seed.MeasureTheory.Constructions.HaarToSphere
public import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The smallest nondegenerate indefinite quadratic band

The scalar MAIS issue #5 candidate reduces its origin calculation to the two-sided band of
the bilinear form `x₀y₀ + x₁y₁`.  Squaring that form gives
`residualGerm 1 1 2`.  This module computes the latter germ's local volume order without the
`EigenvalueLawStatement` frontier and then transfers the result through the square map.

The only integral left after `gaussianLaplace_residualGerm_eq_det` is radial on `ℝ²`:

    ∫ exp (-‖x‖²) / sqrt (1 + T ‖x‖²) dx.

Polar integration turns it into a one-dimensional integral with numerator `r`.  For `T ≥ 3`
that integral is bounded above by `T⁻¹/² ∫ exp (-r²) dr`, and a fixed annulus
`1 < r ≤ 2` supplies a positive lower multiple of `T⁻¹/²`.  Thus the squared germ has
pair `(1/2, 1)`, while the absolute bilinear form has pair `(1, 1)`.

No analytic Morse lemma, eigenvalue law, or asymptotic statement is assumed here.  Every
coordinate transport used by the integral is explicitly measure preserving.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set Filter Topology
open scoped Matrix

/-! ## A multiplicity-one square-root transfer -/

/-! ## The two-dimensional determinant integral -/

/-- A `2×1` real matrix is a two-dimensional Euclidean vector, measurably.-/
@[expose] public noncomputable def matrixTwoOneEquiv :
    Matrix (Fin 2) (Fin 1) ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.curry (Fin 2) (Fin 1) ℝ).symm |>.trans <|
    (MeasurableEquiv.arrowCongr' (Equiv.prodUnique (Fin 2) (Fin 1))
      (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- The radial one-dimensional integral.-/
@[expose] public noncomputable def radialJ2 (T : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), y * Real.exp (-y ^ 2) *
    (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2)

/-- The determinant integral after transporting the `2×1` matrix to `ℝ²`.-/
@[expose] public noncomputable def twoJ (T : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin 2), Real.exp (-‖x‖ ^ 2) *
    (1 + T * ‖x‖ ^ 2) ^ (-(1 : ℝ) / 2)

@[expose] public noncomputable def radialIntegrand (T y : ℝ) : ℝ :=
  y * (Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))

@[expose] public noncomputable def unitDiskVolume : ℝ :=
  volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)

/-! ## Back to the residual germ -/

/-- The unsquared scalar residual, i.e. the dot product of the two hidden vectors.-/
@[expose] public noncomputable def residualAmplitude
    (w : EuclideanSpace ℝ (Fin (2 * 1 + 1 * 2))) : ℝ :=
  (residualY 1 1 2 w * residualX 1 1 2 w) 0 0

end AISafetyAtlas.SingularLearning
