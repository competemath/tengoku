/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
public import Tengoku

/-!
# Zero Free Rectangles

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

end NumberField.Odlyzko
