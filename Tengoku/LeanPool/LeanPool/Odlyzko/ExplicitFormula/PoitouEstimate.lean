/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.CompletedZetaCenterLogBound
public import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.FiniteSetAvoidance
public import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouContourLimit
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarTransform
import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.ZeroFreeRectangles
public import Tengoku

/-!
# Poitou Estimate

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace NumberField.Odlyzko

theorem sq_abs_mul_norm_poitouTransform_regularized_eq_norm_fourier_second
    {δ : ℝ} (hδ : 0 < δ) (y σ t : ℝ) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ =
      ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ)
        (-t / (2 * Real.pi))‖ := by
  let w : ℝ := -t / (2 * Real.pi)
  have hfourier :=
    fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
      hδ y σ w
  have hfactor :
      ‖(((2 * Real.pi : ℂ) * I * (w : ℂ)) ^ 2)‖ = |t| ^ 2 := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs]
    dsimp [w]
    norm_num
    field_simp [Real.pi_ne_zero]
    simp
  have hnorm :
      |t| ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ =
        ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ) w‖ := by simp_all
  rw [poitouTransform_regularizedScaledTartar_eq_fourier]
  grind

theorem tendsto_sq_abs_mul_norm_poitouTransform_regularized_atTop
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Tendsto
      (fun t : ℝ ↦ |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖)
      atTop (𝓝 0) := by
  let f : ℝ → ℂ :=
    poitouVerticalProfileSecondDerivative
      (regularizedScaledTartar y δ)
      (regularizedScaledTartarDerivative y δ)
      (regularizedScaledTartarSecondDerivative y δ) σ
  have hfourier :
      Tendsto (fun t : ℝ ↦ 𝓕 f (-t / (2 * Real.pi)))
        atTop (𝓝 0) := by
    have hzero := Real.zero_at_infty_fourier f
    have hfreq :
        Tendsto (fun t : ℝ ↦ (-1 / (2 * Real.pi)) * t)
          atTop (cocompact ℝ) :=
      (Filter.tendsto_cocompact_mul_left₀
        (show (-1 / (2 * Real.pi) : ℝ) ≠ 0 by positivity)).comp
        atTop_le_cocompact
    convert hzero.comp hfreq using 1
    grind
  have hnorm :
      Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
        atTop (𝓝 0) := by
    have h :=
      continuous_norm.continuousAt.tendsto.comp hfourier
    change Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
      atTop (𝓝 ‖(0 : ℂ)‖) at h
    simpa using h
  convert hnorm using 1
  funext t
  exact sq_abs_mul_norm_poitouTransform_regularized_eq_norm_fourier_second
    hδ y σ t

theorem tendsto_sq_abs_mul_norm_poitouTransform_regularized_atBot
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Tendsto
      (fun t : ℝ ↦ |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖)
      atBot (𝓝 0) := by
  let f : ℝ → ℂ :=
    poitouVerticalProfileSecondDerivative
      (regularizedScaledTartar y δ)
      (regularizedScaledTartarDerivative y δ)
      (regularizedScaledTartarSecondDerivative y δ) σ
  have hzero := Real.zero_at_infty_fourier f
  have hfreq :
      Tendsto (fun t : ℝ ↦ (-1 / (2 * Real.pi)) * t)
        atBot (cocompact ℝ) :=
    (Filter.tendsto_cocompact_mul_left₀
      (show (-1 / (2 * Real.pi) : ℝ) ≠ 0 by positivity)).comp
      atBot_le_cocompact
  have hfourier :
      Tendsto (fun t : ℝ ↦ 𝓕 f (-t / (2 * Real.pi)))
        atBot (𝓝 0) := by
    convert hzero.comp hfreq using 1
    grind
  have hnorm :
      Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
        atBot (𝓝 0) := by
    have h := continuous_norm.continuousAt.tendsto.comp hfourier
    change Tendsto (fun t : ℝ ↦ ‖𝓕 f (-t / (2 * Real.pi))‖)
      atBot (𝓝 ‖(0 : ℂ)‖) at h
    simpa using h
  convert hnorm using 1
  funext t
  exact sq_abs_mul_norm_poitouTransform_regularized_eq_norm_fourier_second
    hδ y σ t

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real

namespace NumberField.Odlyzko

/-- A regularized poitou profile second derivative majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouProfileSecondDerivativeMajorant
    (y δ M x : ℝ) : ℝ :=
  Real.exp (M ^ 2 / (2 * δ)) *
    ((y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
        2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
        2 * M * (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
        M ^ 2 +
        (8 * δ * |y| * tartarAmplitudeDerivativeBound +
          2 * δ + 4 * M * δ) * |x| +
        4 * δ ^ 2 * x ^ 2) *
      Real.exp (-(δ / 2) * x ^ 2))

/-- A regularized poitou strip quadratic decay constant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouStripQuadraticDecayConstant
    (y δ a b : ℝ) : ℝ :=
  ∫ x : ℝ, regularizedPoitouProfileSecondDerivativeMajorant y δ
    (max |a - 1 / 2| |b - 1 / 2|) x

theorem regularizedPoitouProfileSecondDerivativeMajorant_integrable
    {δ : ℝ} (hδ : 0 < δ) (y M : ℝ) :
    Integrable (regularizedPoitouProfileSecondDerivativeMajorant y δ M) := by
  let A :=
    y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
      2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
      2 * M * (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
      M ^ 2
  let B :=
    8 * δ * |y| * tartarAmplitudeDerivativeBound +
      2 * δ + 4 * M * δ
  let C := 4 * δ ^ 2
  have hquad :=
    integrable_quadratic_abs_mul_exp_neg_mul_sq
      (show 0 < δ / 2 by positivity) A B C
  have hconst :
      Integrable (fun x : ℝ ↦
        Real.exp (M ^ 2 / (2 * δ)) *
          ((A + B * |x| + C * x ^ 2) *
            Real.exp (-(δ / 2) * x ^ 2))) :=
    hquad.const_mul _
  apply hconst.congr
  filter_upwards with x
  unfold regularizedPoitouProfileSecondDerivativeMajorant
  grind

theorem norm_poitouVerticalProfileSecondDerivative_regularized_le_majorant
    {δ M : ℝ} (hδ : 0 < δ) (_hM : 0 ≤ M)
    (y : ℝ) {σ : ℝ} (hσ : |σ - 1 / 2| ≤ M) (x : ℝ) :
    ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖ ≤
      regularizedPoitouProfileSecondDerivativeMajorant y δ M x := by
  refine (norm_poitouVerticalProfileSecondDerivative_regularized_le
    hδ y σ x).trans ?_
  unfold regularizedPoitouProfileSecondDerivativeMajorant
  have hA := tartarAmplitudeDerivativeBound_nonneg
  have hA₂ := tartarTestFunctionSecondDerivativeBound_nonneg
  have hexp :
      Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ)) ≤
        Real.exp (M ^ 2 / (2 * δ)) := by
    gcongr
  apply mul_le_mul
  · simp_all
  · gcongr
  · positivity
  · positivity

theorem sq_abs_mul_norm_poitouTransform_regularized_le_strip
    {δ a b : ℝ} (hδ : 0 < δ) (y t : ℝ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      ∫ x : ℝ, regularizedPoitouProfileSecondDerivativeMajorant y δ
        (max |a - 1 / 2| |b - 1 / 2|) x := by
  refine (sq_abs_mul_norm_poitouTransform_regularized_le hδ y σ t).trans ?_
  apply integral_mono
  · exact (poitouVerticalProfileSecondDerivative_regularized_integrable
      hδ y σ).norm
  · exact regularizedPoitouProfileSecondDerivativeMajorant_integrable hδ y _
  · intro x
    apply norm_poitouVerticalProfileSecondDerivative_regularized_le_majorant
      hδ ((abs_nonneg (a - 1 / 2)).trans (le_max_left _ _)) y
    grind

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- Absolute ordinates, in prescribed bands, of zeros of the completed Dedekind zeta function. -/
noncomputable def completedDedekindZetaZeroAbsoluteOrdinatesInBands
    (a b U V : ℝ) : Finset ℝ :=
  ((completedDedekindZetaZerosInClosedRectangle K a b (-V) V).filter
      fun z ↦ U ≤ |z.im|).image fun z ↦ |z.im|

end NumberField.Odlyzko

end

section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height ordinates used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightOrdinates (A : ℝ) : Finset ℝ :=
  completedDedekindZetaZeroAbsoluteOrdinatesInBands K (-3) 7 (A - 5) (A + 6)

open Classical in
/-- A completed zeta selected height separation used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightSeparation (A : ℝ) : ℝ :=
  finiteSetAvoidanceRadiusOnLength 1
    (completedZetaSelectedHeightOrdinates K A)

omit [IsTotallyComplex K] in
open Classical in
theorem completedZetaSelectedHeightSeparation_pos (A : ℝ) :
    0 < completedZetaSelectedHeightSeparation K A :=
  finiteSetAvoidanceRadiusOnLength_pos one_pos _

end NumberField.Odlyzko

end

section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta moving vertical coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingVerticalCoefficient (R : ℝ) : ℝ :=
  max 1
    (poleClearedCompletedDedekindZetaVerticalBound K
      (2 - |R|) (2 + |R|))

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingVerticalCoefficient (R : ℝ) :
    1 ≤ completedZetaMovingVerticalCoefficient K R :=
  le_max_left _ _

/-- A completed zeta moving center log linear bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterLogLinearBound
    (R t : ℝ) : ℝ :=
  max 1 <|
    completedZetaMovingVerticalCoefficient K R +
      2 * (1 + |t| + |R|) +
      Real.log (dedekindZetaInverseVerticalMajorant K) -
      (nrComplexPlaces K : ℝ) / 2 *
        Real.log complexPlaceGammaVerticalLowerConstant +
      (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t|

omit [IsTotallyComplex K] in
theorem log_completedZetaMovingCircleBound_le
    (R t : ℝ) :
    Real.log (completedZetaMovingCircleBound K R t) ≤
      completedZetaMovingVerticalCoefficient K R +
        2 * (1 + |t| + |R|) := by
  let V : ℝ :=
    poleClearedCompletedDedekindZetaVerticalBound K
      (2 - |R|) (2 + |R|)
  let D : ℝ := completedZetaMovingVerticalCoefficient K R
  let Q : ℝ := 1 + |t| + |R|
  have hD : 1 ≤ D := one_le_completedZetaMovingVerticalCoefficient K R
  have hVD : V ≤ D := le_max_right _ _
  have hQ : 1 ≤ Q := by grind
  have hmajor :
      completedZetaMovingCircleBound K R t ≤ D * Q ^ 2 := by
    change max 1 (V * Q ^ 2) ≤ D * Q ^ 2
    apply max_le
    · nlinarith [sq_nonneg Q]
    · exact mul_le_mul_of_nonneg_right hVD (sq_nonneg Q)
  calc
    Real.log (completedZetaMovingCircleBound K R t) ≤
        Real.log (D * Q ^ 2) :=
      Real.log_le_log
        (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaMovingCircleBound K R t)) hmajor
    _ = Real.log D + 2 * Real.log Q := by
      rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hD))
        (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hQ))),
        Real.log_pow]
      norm_num
    _ ≤ D + 2 * Q := by
      gcongr
      · exact Real.log_le_self (zero_le_one.trans hD)
      · exact Real.log_le_self (zero_le_one.trans hQ)
    _ = completedZetaMovingVerticalCoefficient K R +
          2 * (1 + |t| + |R|) := rfl

/-- A completed zeta moving center constant part used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterConstantPart (R : ℝ) : ℝ :=
  completedZetaMovingVerticalCoefficient K R +
    2 * (1 + |R|) +
    |Real.log (dedekindZetaInverseVerticalMajorant K)| +
    (nrComplexPlaces K : ℝ) / 2 *
      |Real.log complexPlaceGammaVerticalLowerConstant|

/-- A completed zeta moving center slope used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterSlope : ℝ :=
  2 + (nrComplexPlaces K : ℝ) / 2 * Real.pi

/-- A completed zeta moving center linear coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCenterLinearCoefficient (R : ℝ) : ℝ :=
  1 + completedZetaMovingCenterConstantPart K R +
    completedZetaMovingCenterSlope K

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingCenterLinearCoefficient (R : ℝ) :
    1 ≤ completedZetaMovingCenterLinearCoefficient K R := by
  have hD : 0 ≤ completedZetaMovingVerticalCoefficient K R :=
    zero_le_one.trans (one_le_completedZetaMovingVerticalCoefficient K R)
  unfold completedZetaMovingCenterLinearCoefficient
  unfold completedZetaMovingCenterConstantPart
  unfold completedZetaMovingCenterSlope
  nlinarith [abs_nonneg R,
    abs_nonneg (Real.log (dedekindZetaInverseVerticalMajorant K)),
    mul_nonneg (by positivity : 0 ≤ (nrComplexPlaces K : ℝ) / 2)
      (abs_nonneg (Real.log complexPlaceGammaVerticalLowerConstant)),
    mul_nonneg (by positivity : 0 ≤ (nrComplexPlaces K : ℝ) / 2)
      Real.pi_pos.le]

omit [IsTotallyComplex K] in
theorem completedZetaMovingCenterLogLinearBound_le
    (R t : ℝ) :
    completedZetaMovingCenterLogLinearBound K R t ≤
      completedZetaMovingCenterLinearCoefficient K R * (1 + |t|) := by
  let P := completedZetaMovingCenterConstantPart K R
  let S := completedZetaMovingCenterSlope K
  let C := completedZetaMovingCenterLinearCoefficient K R
  have hP : 0 ≤ P := by
    dsimp [P, completedZetaMovingCenterConstantPart]
    have hD : 0 ≤ completedZetaMovingVerticalCoefficient K R :=
      zero_le_one.trans (one_le_completedZetaMovingVerticalCoefficient K R)
    positivity
  have hS : 0 ≤ S := by
    dsimp [S, completedZetaMovingCenterSlope]
    positivity
  have hC : C = 1 + P + S := by rfl
  have hraw :
      completedZetaMovingVerticalCoefficient K R +
          2 * (1 + |t| + |R|) +
          Real.log (dedekindZetaInverseVerticalMajorant K) -
          (nrComplexPlaces K : ℝ) / 2 *
            Real.log complexPlaceGammaVerticalLowerConstant +
          (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t| ≤
        P + S * |t| := by
    dsimp [P, S, completedZetaMovingCenterConstantPart,
      completedZetaMovingCenterSlope]
    have hlogC :
        Real.log (dedekindZetaInverseVerticalMajorant K) ≤
          |Real.log (dedekindZetaInverseVerticalMajorant K)| :=
      le_abs_self _
    have hlogG :
        -Real.log complexPlaceGammaVerticalLowerConstant ≤
          |Real.log complexPlaceGammaVerticalLowerConstant| := by grind
    nlinarith [mul_le_mul_of_nonneg_left hlogG (by positivity :
      0 ≤ (nrComplexPlaces K : ℝ) / 2)]
  unfold completedZetaMovingCenterLogLinearBound
  change max 1 _ ≤ C * (1 + |t|)
  apply max_le
  · rw [hC]
    nlinarith [abs_nonneg t]
  · rw [hC]
    calc
      _ ≤ P + S * |t| := hraw
      _ ≤ (1 + P + S) * (1 + |t|) := by
        nlinarith [abs_nonneg t, mul_nonneg hP (abs_nonneg t)]

omit [IsTotallyComplex K] in
theorem completedZetaCenterLogLinearBound_eq_moving (t : ℝ) :
    completedZetaCenterLogLinearBound K t =
      completedZetaMovingCenterLogLinearBound K 6 t := by
  unfold completedZetaCenterLogLinearBound
  unfold completedZetaCenterLogLinearExpression
  unfold completedZetaRadiusSixVerticalCoefficient
  unfold completedZetaMovingCenterLogLinearBound
  unfold completedZetaMovingVerticalCoefficient
  grind

end NumberField.Odlyzko

end

section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height zero count bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightZeroCountBound (A : ℝ) : ℝ :=
  2 * completedZetaMovingCenterLogLinearBound K 9 (A + 1 / 2) /
    Real.log (9 / 8)

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The linear coefficient controlling the completed-zeta zero count at a selected height. -/
noncomputable def completedZetaSelectedHeightZeroCountLinearCoefficient : ℝ :=
  4 * completedZetaMovingCenterLinearCoefficient K 9 / Real.log (9 / 8)

omit [IsTotallyComplex K] in
private theorem completedZetaSelectedHeightZeroCountLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightZeroCountLinearCoefficient K := by
  unfold completedZetaSelectedHeightZeroCountLinearCoefficient
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (zero_le_one.trans
        (one_le_completedZetaMovingCenterLinearCoefficient K 9)))
    (Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)).le

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightZeroCountBound_le_linear
    {A : ℝ} (hA : 6 ≤ A) :
    completedZetaSelectedHeightZeroCountBound K A ≤
      completedZetaSelectedHeightZeroCountLinearCoefficient K * (A + 1) := by
  have hcenter :=
    completedZetaMovingCenterLogLinearBound_le K 9 (A + 1 / 2)
  have habs : |A + 1 / 2| = A + 1 / 2 := abs_of_pos (by linarith)
  rw [habs] at hcenter
  have hlogpos : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  unfold completedZetaSelectedHeightZeroCountBound
  unfold completedZetaSelectedHeightZeroCountLinearCoefficient
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hlogpos).2
  nlinarith [mul_nonneg
    (zero_le_one.trans (one_le_completedZetaMovingCenterLinearCoefficient K 9))
    (show 0 ≤ A + 1 by linarith)]

/-- The linear coefficient controlling inverse zero separation at a selected height. -/
noncomputable def completedZetaSelectedHeightSeparationInvLinearCoefficient : ℝ :=
  4 * (completedZetaSelectedHeightZeroCountLinearCoefficient K + 1)

omit [IsTotallyComplex K] in
private theorem completedZetaSelectedHeightSeparationInvLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightSeparationInvLinearCoefficient K := by
  unfold completedZetaSelectedHeightSeparationInvLinearCoefficient
  exact mul_nonneg (by norm_num)
    (by
      have :=
        completedZetaSelectedHeightZeroCountLinearCoefficient_nonneg K
      linarith)

/-- The linear coefficient controlling the completed zeta function at a selected center. -/
noncomputable def completedZetaSelectedHeightCenterLinearCoefficient : ℝ :=
  2 * completedZetaMovingCenterLinearCoefficient K 6

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightCenterLinearCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightCenterLinearCoefficient K := by
  unfold completedZetaSelectedHeightCenterLinearCoefficient
  exact mul_nonneg (by norm_num)
    (zero_le_one.trans
      (one_le_completedZetaMovingCenterLinearCoefficient K 6))

/-- The quadratic coefficient controlling the completed-zeta logarithmic derivative
at a selected height. -/
noncomputable def completedZetaSelectedHeightLogDerivativeQuadraticCoefficient : ℝ :=
  completedZetaSelectedHeightCenterLinearCoefficient K *
    (completedZetaCanonicalJensenCoefficient *
        completedZetaSelectedHeightSeparationInvLinearCoefficient K +
      completedZetaCanonicalJensenCoefficient + 32)

omit [IsTotallyComplex K] in
theorem completedZetaSelectedHeightLogDerivativeQuadraticCoefficient_nonneg :
    0 ≤ completedZetaSelectedHeightLogDerivativeQuadraticCoefficient K := by
  unfold completedZetaSelectedHeightLogDerivativeQuadraticCoefficient
  exact mul_nonneg
    (completedZetaSelectedHeightCenterLinearCoefficient_nonneg K)
    (by
      have hJ := completedZetaCanonicalJensenCoefficient_pos.le
      have hD :=
        completedZetaSelectedHeightSeparationInvLinearCoefficient_nonneg K
      positivity)

end NumberField.Odlyzko

end

section

open Complex Filter NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory NumberField Real Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

end NumberField.Odlyzko

end

section

open NumberField

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

end NumberField.Odlyzko

end
