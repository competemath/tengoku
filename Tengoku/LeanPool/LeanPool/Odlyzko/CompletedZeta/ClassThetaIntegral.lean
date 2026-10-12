/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassRepresentatives
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ShapeMellinTranslation
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.Defs
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.TotallyComplex
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A shape theta integral constant used in the Odlyzko-bound argument. -/
noncomputable def shapeThetaIntegralConstant : ℝ :=
  2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
    NumberField.Units.regulator K

open Classical in
/-- A class completed theta integral used in the Odlyzko-bound argument. -/
noncomputable def classCompletedThetaIntegral
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s *
    (torsionOrder K : ℂ)⁻¹ *
    (absNorm
      (inverseClassIdealRepresentative K C : Ideal (𝓞 K)) : ℂ) ^ s *
    ((2 : ℂ) ^ nrComplexPlaces K *
      ∫ y in unitFundamentalParamSet K,
        ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
          logarithmicMellinWeight K s y *
          nonzeroIdealShapeTheta K
            (inverseClassIdealRepresentative K C) y)

end NumberField.Odlyzko
