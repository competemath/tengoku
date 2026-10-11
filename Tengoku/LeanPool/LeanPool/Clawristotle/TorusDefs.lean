/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Tengoku

/-!
# Torus Type Definitions and Differential Operators

Defines the 3-torus T^3 = (R/Z)^3, the projection `torusMk`, the periodic lift,
and differential operators (`torusGradX`, `torusDivX`, `torusCurlX`) via the
periodic lift. The `FlatTorus3` instance is assembled in `TorusInstance.lean`.
-/

@[expose] public section

open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- The concrete 3-torus
-- ============================================================================

/-- The 3-torus: product of three circles with period 1. -/
abbrev Torus3 := Fin 3 → AddCircle (1 : ℝ)

-- Period 1 > 0, needed for AddCircle.measureSpace

/-- The quotient map ℝ³ → T³, sending each coordinate to its equivalence class. -/
def torusMk (x : Fin 3 → ℝ) : Torus3 := fun i => QuotientAddGroup.mk (x i)

-- torusMk is surjective (every point in T³ has a preimage)

/-- The periodic lift of a function on the torus to ℝ³. -/
def periodicLift (f : Torus3 → ℝ) : (Fin 3 → ℝ) → ℝ := f ∘ torusMk

-- The lift IS periodic (by construction):

end
