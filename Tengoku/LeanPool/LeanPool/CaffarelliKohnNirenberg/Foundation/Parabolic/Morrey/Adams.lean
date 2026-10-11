/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Maximal.StrongType
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Hedberg
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Inclusions
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Hedberg and Adams estimates

This module connects the parabolic Riesz potential with the exported maximal
function estimates and the cylinder Morrey seminorm.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The maximal function applied to the absolute value of a real function. -/
def parabolicMaximalMajorant (f : ParabolicPoint → ℝ) : ParabolicPoint → ℝ≥0∞ :=
  parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |f w|)

/-- Negative-index dyadic parabolic shell for the near-field Morrey estimate. -/
def nearShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (Int.negSucc n) z

/-- The geometric constant in the local Hedberg estimate. -/
def parabolicHedbergNearConstant (β : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
    ∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)

end Morrey
end Parabolic
end Foundation
end CKN
