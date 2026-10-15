/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredReflection
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaIntegral
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaRadial
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ShapeThetaPeriodicity
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h3v.s7.0bac74b1995b from=translated src=- shape=0a3f2d64 vocab=1b2a90d8
-/
theorem logarithmicMellinWeight_covolumeCenter
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    logarithmicMellinWeight K s
        (radialLogVector K (fractionalShapeCovolumeCenter K I)) =
      (fractionalShapeCovolumeConstant K I : ℂ) ^ (-s) := by
  have hfin : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hA := fractionalShapeCovolumeConstant_pos K I
  rw [logarithmicMellinWeight, radialLogVector_apply_w₀,
    fractionalShapeCovolumeCenter]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne')]
  rw [← Complex.ofReal_log hA.le]
  simp_all

open Classical in
/--
@isnad1 id=eq.1h2v.s5.d92e3905cf9f from=translated src=- shape=b4eaa25e vocab=11d4a305
-/
theorem ofReal_sqrt_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (Real.sqrt x : ℂ) ^ s = (x : ℂ) ^ (s / 2) := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log (Real.sqrt_nonneg x),
    ← Complex.ofReal_log hx.le, Real.log_sqrt hx.le]
  push_cast
  ring_nf

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h4v.s7.9eb6abf562b5 from=translated src=- shape=33802681 vocab=629da54b
-/
theorem centeredNonzeroFractionalShapeThetaMellinKernel_eq_covolume_mul
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    centeredNonzeroFractionalShapeThetaMellinKernel K I s y =
      (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
        nonzeroFractionalShapeThetaMellinKernel K I s
          (centeredFractionalShapeCoordinates K I y) := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    nonzeroFractionalShapeThetaMellinKernel]
  rw [show
      logarithmicMellinWeight K s
          (centeredFractionalShapeCoordinates K I y) =
        logarithmicMellinWeight K s y *
          logarithmicMellinWeight K s
            (radialLogVector K
              (fractionalShapeCovolumeCenter K I)) by
    simpa only [centeredFractionalShapeCoordinates, mul_comm] using
      logarithmicMellinWeight_add K s y
        (radialLogVector K (fractionalShapeCovolumeCenter K I))]
  rw [
    logarithmicMellinWeight_covolumeCenter,
    Complex.cpow_neg]
  have hpow :
      (fractionalShapeCovolumeConstant K I : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Complex.ofReal_ne_zero.mpr
        (fractionalShapeCovolumeConstant_pos K I).ne'
  grind

open Classical in
/--
@isnad1 id=eq.0h5v.s8.52acbed34c63 from=translated src=- shape=8469626e vocab=8c57cd39
-/
theorem nonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (g : unitCoordinateLattice (K := K))
    (y : mixedEmbedding.realSpace K) :
    nonzeroFractionalShapeThetaMellinKernel K I s
        ((g : mixedEmbedding.realSpace K) + y) =
      nonzeroFractionalShapeThetaMellinKernel K I s y := by
  rw [nonzeroFractionalShapeThetaMellinKernel,
    nonzeroFractionalShapeThetaMellinKernel,
    logarithmicMellinWeight_vadd_unitCoordinateLattice]
  congr 1
  obtain ⟨z, hz⟩ := g.prop
  rw [← hz]
  simpa only [unitCoordinateShiftHom_apply, add_comm] using
    congrArg (fun z : ℂ ↦ z - 1)
      (fractionalShapeIdealTheta_add_unitCoordinateShift K I y z)

open Classical in
/--
@isnad1 id=eq.0h3v.s8.a1c07b8c1915 from=translated src=- shape=4376e7cb vocab=530a5f0e
-/
theorem setIntegral_centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K I s y := by
  calc
    (∫ y in unitFundamentalParamSet K,
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        ∫ y in unitFundamentalParamSet K,
          (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
            nonzeroFractionalShapeThetaMellinKernel K I s
              (y + radialLogVector K
                (fractionalShapeCovolumeCenter K I)) := by
      apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
      intro y _
      simpa only [centeredFractionalShapeCoordinates] using
        centeredNonzeroFractionalShapeThetaMellinKernel_eq_covolume_mul
          K I s y
    _ = (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K I s
              (y + radialLogVector K
                (fractionalShapeCovolumeCenter K I)) := by
      rw [integral_const_mul]
    _ = (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K I s y := by
      rw [setIntegral_unitFundamentalParamSet_add_eq
        (nonzeroFractionalShapeThetaMellinKernel K I s)
        (nonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
          K I s)
        (radialLogVector K (fractionalShapeCovolumeCenter K I))]

open Classical in
/-- A centered class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaIntegral
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    ∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K
          (inverseClassIdealRepresentative K C)) s y

end NumberField.Odlyzko

end

section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered positive class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredPositiveClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∫ y in positiveUnitFundamentalParamSet (K := K),
    centeredNonzeroFractionalShapeThetaMellinKernel K I s y

open Classical in
/-- A centered class theta pole term used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaPoleTerm (s : ℂ) : ℂ :=
  -1 / ((Module.finrank ℚ K : ℂ) * (1 - s)) -
    1 / ((Module.finrank ℚ K : ℂ) * s)

open Classical in
/-- A centered radially continued class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredRadiallyContinuedClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  centeredPositiveClassThetaIntegral K I s +
    centeredPositiveClassThetaIntegral K
      (traceDualIdealUnit K I) (1 - s) +
    centeredClassThetaPoleTerm K s

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.1h2v.s7.6d3c8698e94b from=translated src=- shape=a437bede vocab=f0ad4ed0
-/
theorem setIntegral_centeredClassThetaPoissonCorrection_eq_poleTerm
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y in positiveUnitFundamentalParamSet (K := K),
      centeredClassThetaPoissonCorrection K s y) =
        centeredClassThetaPoleTerm K s := by
  rw [setIntegral_centeredClassThetaPoissonCorrection K hs,
    centeredClassThetaPoleTerm]

open Classical in
/-- A centered continued class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredContinuedClassThetaIntegral
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    centeredRadiallyContinuedClassThetaIntegral K
      (FractionalIdeal.mk0 K
        (inverseClassIdealRepresentative K C)) s

end NumberField.Odlyzko

end
