/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.Seed.Probability.Distributions.Gamma
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Gamma law's Laplace transform

Home: none (standard analysis in Mathlib's types: four facts about `ProbabilityTheory.gammaMeasure`,
with no programme vocabulary; ref: @feller2009introduction, Ch. XIII §2, p. 435)

Four facts about Mathlib's `ProbabilityTheory.gammaMeasure`: integration against it is
integration against its density on `(0, ∞)` (`lintegral_gammaMeasure`); its Laplace transform
against `u^q e^{-su}` (`lintegral_gammaMeasure_rpow_mul_exp`, the one computation a Gamma-mixture
argument needs both for the transform and for the moments); and that it lives on the positive
axis (`gammaMeasure_Iio_zero`, `ae_pos_gammaMeasure`).

Moved from Paper V's cone export (`cone-v0.1`, `f28c066e`, `SpatialLine.MaternMixture`),
statements unchanged up to the namespace. Second demand: Paper V's `matern_gamma_mixture` and
Paper VII's `lintegral_exp_gammaMeasure`/`ae_nonneg_gammaMeasure`
(`Formalization/AffineHemigroup/MaternOrbit.lean`), the case `q = 0`, `r = 1`, both read
`lintegral_gammaMeasure_rpow_mul_exp`. Everything here is proved from Mathlib's gamma-measure and
Gaussian-integral lemmas alone.

## References

* @feller2009introduction, Ch. XIII §2, Examples (a)–(b), p. 435: the Laplace transform of the
  gamma density `f_{1,ν}` is `(1 + λ)^{-ν}` (via the power density `u_α(x) = x^{α-1}/Γ(α)`'s
  transform `λ^{-α}` and the translation rule) — `lintegral_gammaMeasure_rpow_mul_exp` is this
  fact at a general rate `r` and with the extra power `u^q`.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

/-- Integration against the Gamma law is integration against its density on `(0,∞)`.-/
theorem lintegral_gammaMeasure {a r : ℝ} {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ u, g u ∂(gammaMeasure a r))
      = ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ a / Real.Gamma a * u ^ (a - 1) * Real.exp (-(r * u))) * g u := by
  have hpdfm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hpdfm hg]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun u => gammaPDF a r u * g u) (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hneg : (∫⁻ u in Iio (0 : ℝ), gammaPDF a r u * g u) = 0 := by
    refine (setLIntegral_congr_fun measurableSet_Iio fun u hu => ?_).trans lintegral_zero
    rw [gammaPDF_of_neg hu, zero_mul]
  have hIci : (∫⁻ u in Ici (0 : ℝ), gammaPDF a r u * g u)
      = ∫⁻ u in Ioi (0 : ℝ), gammaPDF a r u * g u :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hneg, hIci, zero_add] at hsplit
  simp only [Pi.mul_apply]
  rw [← hsplit]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [gammaPDF_of_nonneg (le_of_lt hu)]

/-- The Gamma law lives on the positive axis.-/
theorem gammaMeasure_Iio_zero (a r : ℝ) : gammaMeasure a r (Iio (0 : ℝ)) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ u ∂(gammaMeasure a r), 0 < u := by
  have hIic : gammaMeasure a r (Iic (0 : ℝ)) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
      setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [ae_iff]
  convert hIic using 2
  ext u; simp

end ScaleSpace
