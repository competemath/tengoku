import Tengoku

/-!
# Finite-dimensional Gaussian KL backend

This module provides a concrete finite-dimensional Gaussian parameter surface
for PAC-Bayes examples. The prior and posterior are actual measures on
`Fin d → ℝ`, represented by Lebesgue density via `volume.withDensity`.

The KL backend is the closed-form relative entropy for diagonal Gaussian
families. The proved spherical formula is the standard finite-dimensional
identity

`KL(N(m, σ² I) || N(0, τ² I)) =
  (d * (σ² / τ² - 1 + log (τ² / σ²)) + ||m||² / τ²) / 2`.

The file does not claim a general measure-theoretic KL integral theorem for
arbitrary densities. It gives the analytic KL of the concrete Gaussian measure
family used by the PAC-Bayes compiler examples.
-/

namespace FormalSLT.PACBayes

open MeasureTheory
open Finset Real BigOperators

noncomputable section

/-- Parameter space for a `d`-dimensional real Gaussian. -/
abbrev GaussianParameterSpace (d : ℕ) := Fin d → ℝ

/-- Diagonal finite-dimensional Gaussian parameters. -/
structure DiagonalGaussianParams (d : ℕ) where
  mean : GaussianParameterSpace d
  variance : Fin d → ℝ
  variance_pos : ∀ i, 0 < variance i

/-- Spherical finite-dimensional Gaussian parameters. -/
structure SphericalGaussianParams (d : ℕ) where
  mean : GaussianParameterSpace d
  variance : ℝ
  variance_pos : 0 < variance

namespace SphericalGaussianParams

/-- Convert a spherical Gaussian to a diagonal Gaussian with constant variance. -/
def toDiagonal {d : ℕ} (params : SphericalGaussianParams d) :
    DiagonalGaussianParams d where
  mean := params.mean
  variance := fun _ => params.variance
  variance_pos := fun _ => params.variance_pos

end SphericalGaussianParams

/-- One-dimensional Gaussian density factor. -/
def gaussianCoordinateDensity (mean variance x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * variance))⁻¹ *
    Real.exp (-((x - mean) ^ (2 : Nat)) / (2 * variance))

/-- Product density for a diagonal Gaussian on `Fin d → ℝ`. -/
def diagonalGaussianDensity {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) : ℝ :=
  ∏ i, gaussianCoordinateDensity (params.mean i) (params.variance i) (x i)

/-- The one-dimensional Gaussian density factor is nonnegative.
@isnad1 id=le.0h3v.s4.4d8593605e6e from=translated src=- shape=ac9c39a3 vocab=f5c425ac
-/
theorem gaussianCoordinateDensity_nonneg (mean variance x : ℝ) :
    0 ≤ gaussianCoordinateDensity mean variance x := by
  unfold gaussianCoordinateDensity
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- The product density for a diagonal Gaussian is nonnegative.
@isnad1 id=le.0h3v.s4.d68015e6632e from=translated src=- shape=d78b0cc0 vocab=516138d9
-/
theorem diagonalGaussianDensity_nonneg {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) :
    0 ≤ diagonalGaussianDensity params x := by
  unfold diagonalGaussianDensity
  exact Finset.prod_nonneg
    (fun i _ => gaussianCoordinateDensity_nonneg (params.mean i) (params.variance i) (x i))

/-- ENNReal-valued density used to construct the Gaussian measure. -/
def diagonalGaussianENNRealDensity {d : ℕ}
    (params : DiagonalGaussianParams d) (x : GaussianParameterSpace d) : ENNReal :=
  ENNReal.ofReal (diagonalGaussianDensity params x)

/-- Diagonal Gaussian measure on `Fin d → ℝ`, represented by its Lebesgue density. -/
def diagonalGaussianMeasure {d : ℕ}
    (params : DiagonalGaussianParams d) : Measure (GaussianParameterSpace d) :=
  volume.withDensity (diagonalGaussianENNRealDensity params)

/-- A diagonal Gaussian measure is absolutely continuous with respect to volume.
@isnad1 id=absolute.0h2v.s5.e10196033e0b from=translated src=- shape=33820980 vocab=78598949
-/
theorem diagonalGaussianMeasure_absolutelyContinuous_volume {d : ℕ}
    (params : DiagonalGaussianParams d) :
    diagonalGaussianMeasure params ≪ volume := by
  unfold diagonalGaussianMeasure
  exact withDensity_absolutelyContinuous volume (diagonalGaussianENNRealDensity params)

/-- Spherical Gaussian measure on `Fin d → ℝ`. -/
def sphericalGaussianMeasure {d : ℕ}
    (params : SphericalGaussianParams d) : Measure (GaussianParameterSpace d) :=
  diagonalGaussianMeasure params.toDiagonal

/-- A spherical Gaussian measure is absolutely continuous with respect to volume.
@isnad1 id=absolute.0h2v.s5.1c87cbc415f7 from=translated src=- shape=33820980 vocab=2eabc9c5
-/
theorem sphericalGaussianMeasure_absolutelyContinuous_volume {d : ℕ}
    (params : SphericalGaussianParams d) :
    sphericalGaussianMeasure params ≪ volume := by
  exact diagonalGaussianMeasure_absolutelyContinuous_volume params.toDiagonal

/-- Closed-form diagonal Gaussian KL, posterior first and prior second. -/
def diagonalGaussianKL {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) : ℝ :=
  ∑ i, (posterior.variance i / prior.variance i +
      (posterior.mean i - prior.mean i) ^ (2 : Nat) / prior.variance i -
      1 + Real.log (prior.variance i / posterior.variance i)) / 2

/-- Named closed form for the diagonal Gaussian KL formula. -/
def diagonalGaussianKLClosedForm {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) : ℝ :=
  ∑ i, (posterior.variance i / prior.variance i +
      (posterior.mean i - prior.mean i) ^ (2 : Nat) / prior.variance i -
      1 + Real.log (prior.variance i / posterior.variance i)) / 2

/-- The diagonal Gaussian KL backend is the standard coordinatewise closed form.
@isnad1 id=eq.0h3v.s4.24682494d732 from=translated src=- shape=1acb4e4b vocab=020c0b31
-/
theorem diagonalGaussianKL_eq_sum_closedForm {d : ℕ}
    (posterior prior : DiagonalGaussianParams d) :
    diagonalGaussianKL posterior prior =
      diagonalGaussianKLClosedForm posterior prior := by
  rfl

/-- Squared Euclidean distance between two Gaussian mean vectors. -/
def squaredMeanDistance {d : ℕ}
    (posteriorMean priorMean : GaussianParameterSpace d) : ℝ :=
  ∑ i, (posteriorMean i - priorMean i) ^ (2 : Nat)

/-- Spherical Gaussian KL, posterior first and prior second. -/
def sphericalGaussianKL {d : ℕ}
    (posterior prior : SphericalGaussianParams d) : ℝ :=
  diagonalGaussianKL posterior.toDiagonal prior.toDiagonal

/-- Closed-form KL for spherical finite-dimensional Gaussians. -/
def sphericalGaussianKLClosedForm {d : ℕ}
    (posterior prior : SphericalGaussianParams d) : ℝ :=
  ((d : ℝ) *
      (posterior.variance / prior.variance - 1 +
        Real.log (prior.variance / posterior.variance)) +
      squaredMeanDistance posterior.mean prior.mean / prior.variance) /
    2

/-- Spherical Gaussian KL formula.
@isnad1 id=eq.0h3v.s4.350eb2a9a2d0 from=translated src=- shape=1acb4e4b vocab=139264b0
-/
theorem sphericalGaussianKL_eq_closedForm {d : ℕ}
    (posterior prior : SphericalGaussianParams d) :
    sphericalGaussianKL posterior prior =
      sphericalGaussianKLClosedForm posterior prior := by
  unfold sphericalGaussianKL diagonalGaussianKL SphericalGaussianParams.toDiagonal
    sphericalGaussianKLClosedForm squaredMeanDistance
  calc
    (∑ i : Fin d, (posterior.variance / prior.variance +
        (posterior.mean i - prior.mean i) ^ (2 : Nat) / prior.variance -
        1 + Real.log (prior.variance / posterior.variance)) / 2)
        =
      ∑ i : Fin d,
        ((posterior.variance / prior.variance - 1 +
              Real.log (prior.variance / posterior.variance)) +
            (posterior.mean i - prior.mean i) ^ (2 : Nat) /
              prior.variance) / 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ =
      ((d : ℝ) *
          (posterior.variance / prior.variance - 1 +
            Real.log (prior.variance / posterior.variance)) +
          (∑ i : Fin d,
            (posterior.mean i - prior.mean i) ^ (2 : Nat)) /
            prior.variance) /
        2 := by
        let a : ℝ :=
          posterior.variance / prior.variance - 1 +
            Real.log (prior.variance / posterior.variance)
        change
          (∑ i : Fin d,
            (a + (posterior.mean i - prior.mean i) ^ (2 : Nat) /
              prior.variance) / 2) =
          ((d : ℝ) * a +
              (∑ i : Fin d,
                (posterior.mean i - prior.mean i) ^ (2 : Nat)) /
                prior.variance) /
            2
        calc
          (∑ i : Fin d,
            (a + (posterior.mean i - prior.mean i) ^ (2 : Nat) /
              prior.variance) / 2)
              =
            ∑ i : Fin d,
              (a / 2 +
                ((posterior.mean i - prior.mean i) ^ (2 : Nat) /
                  prior.variance) / 2) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              ring
          _ =
            (∑ _i : Fin d, a / 2) +
              ∑ i : Fin d,
                ((posterior.mean i - prior.mean i) ^ (2 : Nat) /
                  prior.variance) / 2 := by
              rw [Finset.sum_add_distrib]
          _ =
            (d : ℝ) * a / 2 +
              ((∑ i : Fin d,
                (posterior.mean i - prior.mean i) ^ (2 : Nat)) /
                prior.variance) / 2 := by
              rw [Finset.sum_const, Finset.sum_div, Finset.sum_div]
              simp [nsmul_eq_mul]
              ring
          _ =
            ((d : ℝ) * a +
                (∑ i : Fin d,
                  (posterior.mean i - prior.mean i) ^ (2 : Nat)) /
                  prior.variance) /
              2 := by
              ring

/-- KL formula for `N(m, σ² I)` against the zero-mean prior `N(0, τ² I)`.
@isnad1 id=eq.2h4v.s7.0310a1708398 from=translated src=- shape=4fc78f23 vocab=017a65e3
-/
theorem sphericalGaussianKL_zeroMeanPrior_eq_closedForm
    {d : ℕ} (mean : GaussianParameterSpace d)
    {posteriorVariance priorVariance : ℝ}
    (hposteriorVariance : 0 < posteriorVariance)
    (hpriorVariance : 0 < priorVariance) :
    sphericalGaussianKL
        { mean := mean
          variance := posteriorVariance
          variance_pos := hposteriorVariance }
        { mean := fun _ => 0
          variance := priorVariance
          variance_pos := hpriorVariance } =
      ((d : ℝ) *
          (posteriorVariance / priorVariance - 1 +
            Real.log (priorVariance / posteriorVariance)) +
          squaredMeanDistance mean (fun _ => 0) / priorVariance) /
        2 := by
  rw [sphericalGaussianKL_eq_closedForm]
  rfl

/-- Equal-variance spherical Gaussian KL collapses to the squared mean distance term.
@isnad1 id=eq.1h4v.s6.f937590829fd from=translated src=- shape=17e13616 vocab=45ef6ffa
-/
theorem sphericalGaussianKL_equalVariance_eq
    {d : ℕ} (posteriorMean priorMean : GaussianParameterSpace d)
    {variance : ℝ} (hvariance : 0 < variance) :
    sphericalGaussianKL
        { mean := posteriorMean
          variance := variance
          variance_pos := hvariance }
        { mean := priorMean
          variance := variance
          variance_pos := hvariance } =
      squaredMeanDistance posteriorMean priorMean / (2 * variance) := by
  rw [sphericalGaussianKL_eq_closedForm]
  have hne : variance ≠ 0 := ne_of_gt hvariance
  simp [sphericalGaussianKLClosedForm, squaredMeanDistance, hne]
  field_simp [hne]

end

end FormalSLT.PACBayes
