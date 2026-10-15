/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredHolomorphy
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.TraceDualClass
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredRepresentative
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

end NumberField.Odlyzko

end

section

open Complex Filter Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors Topology

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- An ideal completed theta integral used in the Odlyzko-bound argument. -/
noncomputable def idealCompletedThetaIntegral
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s *
    (torsionOrder K : ℂ)⁻¹ *
    (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
    ((2 : ℂ) ^ nrComplexPlaces K *
      ∫ y in unitFundamentalParamSet K,
        ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
          logarithmicMellinWeight K s y *
          nonzeroIdealShapeTheta K J y)

open Classical in
/-- A centered fractional class contribution used in the Odlyzko-bound argument. -/
noncomputable def centeredFractionalClassContribution
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    centeredRadiallyContinuedClassThetaIntegral K I s

open Classical in
/-- A pole cleared centered fractional class contribution used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCenteredFractionalClassContribution
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    poleClearedCenteredClassThetaIntegral K I s

end NumberField.Odlyzko

end

section

open Complex Ideal NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h3v.s7.2086442110ec from=translated src=- shape=b583e0ff vocab=af523251
-/
theorem poleClearedCenteredClassThetaIntegral_functionalEquation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    poleClearedCenteredClassThetaIntegral K I s =
      poleClearedCenteredClassThetaIntegral K
        (traceDualIdealUnit K I) (1 - s) := by
  rw [poleClearedCenteredClassThetaIntegral,
    poleClearedCenteredClassThetaIntegral,
    traceDualIdealUnit_traceDualIdealUnit]
  ring_nf

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h3v.s7.efb08a5dc6a1 from=translated src=- shape=b583e0ff vocab=8b82e427
-/
theorem poleClearedCenteredFractionalClassContribution_functionalEquation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    poleClearedCenteredFractionalClassContribution K I s =
      poleClearedCenteredFractionalClassContribution K
        (traceDualIdealUnit K I) (1 - s) := by
  rw [poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredClassThetaIntegral_functionalEquation]

open Classical in
/-- A pole cleared completed dedekind zeta continuation used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCompletedDedekindZetaContinuation (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K),
    poleClearedCenteredFractionalClassContribution K
      (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) s

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h2v.s13.ef9738ca22e8 from=translated src=- shape=ff86c489 vocab=cc350e92
-/
theorem mk_traceDual_inverseClassIdealRepresentative_eq_reindexed
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) =
      ClassGroup.mk K
        (FractionalIdeal.mk0 K
          (inverseClassIdealRepresentative K
            (traceDualInverseClassEquiv K C))) := by
  rw [mk_traceDualIdealUnit_eq_traceDualClassEquiv,
    ClassGroup.mk_mk0, ClassGroup.mk_mk0,
    mk0_inverseClassIdealRepresentative,
    mk0_inverseClassIdealRepresentative,
    traceDualInverseClassEquiv_apply, inv_inv]

end NumberField.Odlyzko

end
