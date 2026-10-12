/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredContinuation
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredRepresentative
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Filter Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors Topology

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem norm_logarithmicMellinWeight
    (s : ℂ) (y : mixedEmbedding.realSpace K) :
    ‖logarithmicMellinWeight K s y‖ =
      Real.exp (y w₀ * (Module.finrank ℚ K : ℝ) * s.re) := by
  rw [logarithmicMellinWeight, norm_exp]
  simp

omit [IsTotallyComplex K] in
open Classical in
theorem norm_logarithmicMellinWeight_mono
    {s : ℂ} {b : ℝ} {y : mixedEmbedding.realSpace K}
    (hy : 0 ≤ y w₀) (hsb : s.re ≤ b) :
    ‖logarithmicMellinWeight K s y‖ ≤
      ‖logarithmicMellinWeight K (b : ℂ) y‖ := by
  rw [norm_logarithmicMellinWeight,
    norm_logarithmicMellinWeight]
  apply Real.exp_le_exp.mpr
  simp only [ofReal_re]
  have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hsb (mul_nonneg hy hn)

omit [IsTotallyComplex K] in
open Classical in
theorem norm_centeredNonzeroFractionalShapeThetaMellinKernel_mono
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} {b : ℝ} {y : mixedEmbedding.realSpace K}
    (hy : 0 ≤ y w₀) (hsb : s.re ≤ b) :
    ‖centeredNonzeroFractionalShapeThetaMellinKernel K I s y‖ ≤
      ‖centeredNonzeroFractionalShapeThetaMellinKernel K I (b : ℂ) y‖ := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_logarithmicMellinWeight_mono K hy hsb) (norm_nonneg _)

open Classical in
/-- A centered mellin radial coefficient used in the Odlyzko-bound argument. -/
noncomputable def centeredMellinRadialCoefficient
    (y : mixedEmbedding.realSpace K) : ℂ :=
  (y w₀ * (Module.finrank ℚ K : ℝ) : ℝ)

omit [IsTotallyComplex K] in
open Classical in
theorem hasDerivAt_centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    HasDerivAt
      (fun z ↦ centeredNonzeroFractionalShapeThetaMellinKernel K I z y)
      (centeredMellinRadialCoefficient K y *
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) s := by
  let c : ℂ := (y w₀ * (Module.finrank ℚ K : ℝ) : ℝ)
  let A : ℂ :=
    fractionalShapeIdealTheta K I
      (expMapBasis (centeredFractionalShapeCoordinates K I y))
      (fun w ↦
        (expMapBasis_pos
          (centeredFractionalShapeCoordinates K I y) w).ne') - 1
  change HasDerivAt (fun z ↦ Complex.exp (c * z) * A)
    (c * (Complex.exp (c * s) * A)) s
  simpa only [id_eq, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id s).const_mul c).cexp.mul_const A)

omit [IsTotallyComplex K] in
open Classical in
theorem norm_centeredMellinRadialCoefficient_mul_kernel_le
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} {b : ℝ} {y : mixedEmbedding.realSpace K}
    (hy : 0 ≤ y w₀) (hsb : s.re + 1 ≤ b) :
    ‖centeredMellinRadialCoefficient K y *
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y‖ ≤
      ‖centeredNonzeroFractionalShapeThetaMellinKernel K I (b : ℂ) y‖ := by
  let t : ℝ := y w₀ * (Module.finrank ℚ K : ℝ)
  have ht : 0 ≤ t := mul_nonneg hy (by positivity)
  have htexp : t ≤ Real.exp t :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp t)
  have hweight :
      t * Real.exp (t * s.re) ≤ Real.exp (t * b) := by
    calc
      t * Real.exp (t * s.re) ≤ Real.exp t * Real.exp (t * s.re) :=
        mul_le_mul_of_nonneg_right htexp (Real.exp_pos _).le
      _ = Real.exp (t * (s.re + 1)) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (t * b) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsb ht)
  rw [norm_mul, centeredMellinRadialCoefficient, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    norm_mul, norm_mul, norm_logarithmicMellinWeight,
    norm_logarithmicMellinWeight]
  simp only [Complex.ofReal_re]
  dsimp [t] at hweight
  calc
    _ = (y w₀ * (Module.finrank ℚ K : ℝ) *
          Real.exp (y w₀ * (Module.finrank ℚ K : ℝ) * s.re)) *
        ‖fractionalShapeIdealTheta K I
          (expMapBasis (centeredFractionalShapeCoordinates K I y))
          (fun w ↦
            (expMapBasis_pos
              (centeredFractionalShapeCoordinates K I y) w).ne') - 1‖ := by ring
    _ ≤ Real.exp (y w₀ * (Module.finrank ℚ K : ℝ) * b) *
        ‖fractionalShapeIdealTheta K I
          (expMapBasis (centeredFractionalShapeCoordinates K I y))
          (fun w ↦
            (expMapBasis_pos
              (centeredFractionalShapeCoordinates K I y) w).ne') - 1‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg _)

open Classical in
/-- A pole cleared centered class theta integral used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCenteredClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (Module.finrank ℚ K : ℂ) * s * (1 - s) *
      (centeredPositiveClassThetaIntegral K I s +
        centeredPositiveClassThetaIntegral K
          (traceDualIdealUnit K I) (1 - s)) - 1

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCenteredClassThetaIntegral_eq_mul_continued
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    poleClearedCenteredClassThetaIntegral K I s =
      (Module.finrank ℚ K : ℂ) * s * (1 - s) *
        centeredRadiallyContinuedClassThetaIntegral K I s := by
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  rw [poleClearedCenteredClassThetaIntegral,
    centeredRadiallyContinuedClassThetaIntegral,
    centeredClassThetaPoleTerm]
  grind

end NumberField.Odlyzko
