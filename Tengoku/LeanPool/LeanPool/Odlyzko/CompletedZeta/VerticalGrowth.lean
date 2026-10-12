/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredRepresentative
public import Tengoku

/-!
# Vertical Growth

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem abs_le_max_abs_endpoints {a b σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    |σ| ≤ max |a| |b| := by grind

/-- A centered class theta vertical radius used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaVerticalRadius (a b : ℝ) : ℝ :=
  max (max |a| |b|) (max |1 - b| |1 - a|) + 1

theorem one_le_centeredClassThetaVerticalRadius (a b : ℝ) :
    1 ≤ centeredClassThetaVerticalRadius a b := by
  unfold centeredClassThetaVerticalRadius
  simp

theorem norm_vertical_pole_factors_le
    {a b σ t : ℝ} (hσ : σ ∈ Set.Icc a b) :
    ‖(σ : ℂ) + t * I‖ ≤
        centeredClassThetaVerticalRadius a b * (1 + |t|) ∧
      ‖1 - ((σ : ℂ) + t * I)‖ ≤
        centeredClassThetaVerticalRadius a b * (1 + |t|) := by
  let D := centeredClassThetaVerticalRadius a b
  have hD : 1 ≤ D := one_le_centeredClassThetaVerticalRadius a b
  have hσabs : |σ| ≤ D := by
    refine (abs_le_max_abs_endpoints hσ).trans ?_
    dsimp [D, centeredClassThetaVerticalRadius]
    grind
  have honesub : |1 - σ| ≤ D := by
    have hmem : 1 - σ ∈ Set.Icc (1 - b) (1 - a) := by
      grind
    refine (abs_le_max_abs_endpoints hmem).trans ?_
    dsimp [D, centeredClassThetaVerticalRadius]
    grind
  have ht : 0 ≤ |t| := abs_nonneg t
  constructor
  · calc
      ‖(σ : ℂ) + t * I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ ≤ D + |t| := add_le_add hσabs le_rfl
      _ ≤ D * (1 + |t|) := by nlinarith
  · have heq :
        1 - ((σ : ℂ) + t * I) = ((1 - σ : ℝ) : ℂ) + (-t) * I := by
      apply Complex.ext <;> simp
    calc
      ‖1 - ((σ : ℂ) + t * I)‖ =
          ‖((1 - σ : ℝ) : ℂ) + (-t) * I‖ := by simp_all
      _ ≤ ‖((1 - σ : ℝ) : ℂ)‖ + ‖(-(t : ℂ)) * I‖ :=
        norm_add_le _ _
      _ = |1 - σ| + |t| := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one]
      _ ≤ D + |t| := add_le_add honesub le_rfl
      _ ≤ D * (1 + |t|) := by nlinarith

/-- A centered positive class theta norm bound used in the Odlyzko-bound argument. -/
noncomputable def centeredPositiveClassThetaNormBound
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ℝ) : ℝ :=
  ∫ y in positiveUnitFundamentalParamSet (K := K),
    ‖centeredNonzeroFractionalShapeThetaMellinKernel K
      (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) (b : ℂ) y‖

omit [IsTotallyComplex K] in
theorem centeredPositiveClassThetaNormBound_nonneg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ℝ) :
    0 ≤ centeredPositiveClassThetaNormBound K I b :=
  integral_nonneg fun _ ↦ norm_nonneg _

/-- A pole cleared centered class theta vertical bound used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCenteredClassThetaVerticalBound
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : ℝ) : ℝ :=
  (Module.finrank ℚ K : ℝ) *
      (centeredPositiveClassThetaNormBound K I b +
        centeredPositiveClassThetaNormBound K (traceDualIdealUnit K I) (1 - a)) *
      centeredClassThetaVerticalRadius a b ^ 2 + 1

omit [IsTotallyComplex K] in
theorem poleClearedCenteredClassThetaVerticalBound_nonneg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : ℝ) :
    0 ≤ poleClearedCenteredClassThetaVerticalBound K I a b := by
  unfold poleClearedCenteredClassThetaVerticalBound
  have hI := centeredPositiveClassThetaNormBound_nonneg K I b
  have hdual :=
    centeredPositiveClassThetaNormBound_nonneg K (traceDualIdealUnit K I) (1 - a)
  positivity

end NumberField.Odlyzko

end

section

open Complex Ideal NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered fractional class normalization norm used in the Odlyzko-bound argument. -/
noncomputable def centeredFractionalClassNormalizationNorm : ℝ :=
  ‖(torsionOrder K : ℂ)⁻¹ *
      (2 : ℂ) ^ nrComplexPlaces K *
      (shapeThetaIntegralConstant K : ℂ)‖

open Classical in
/-- A pole cleared completed dedekind zeta vertical bound used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCompletedDedekindZetaVerticalBound
    (a b : ℝ) : ℝ :=
  ∑ C : ClassGroup (𝓞 K),
    centeredFractionalClassNormalizationNorm K *
      poleClearedCenteredClassThetaVerticalBound K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCompletedDedekindZetaVerticalBound_nonneg (a b : ℝ) :
    0 ≤ poleClearedCompletedDedekindZetaVerticalBound K a b := by
  unfold poleClearedCompletedDedekindZetaVerticalBound
  apply Finset.sum_nonneg
  intro C _
  exact mul_nonneg
    (norm_nonneg _)
    (poleClearedCenteredClassThetaVerticalBound_nonneg K _ a b)

end NumberField.Odlyzko

end
