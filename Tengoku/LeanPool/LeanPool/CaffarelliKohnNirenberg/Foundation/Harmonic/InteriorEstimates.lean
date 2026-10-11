/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import Tengoku

/-!
# Interior Estimates

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

/-- Coefficient in the interior supremum estimate for a harmonic function. -/
noncomputable def harmonicInteriorSupConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (harmonicInteriorSourceConstant + 6 * harmonicInteriorGradientConstant)

/-- Coefficient in the interior supremum estimate for the harmonic gradient. -/
noncomputable def harmonicInteriorGradientSupConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (harmonicInteriorSourceGradientConstant +
      6 * harmonicInteriorKernelXGradientConstant)

lemma harmonicInteriorGradientSupConstant_nonneg :
    0 ≤ harmonicInteriorGradientSupConstant := by
  dsimp [harmonicInteriorGradientSupConstant]
  have hS := harmonicInteriorSourceGradientConstant_nonneg
  have hK := harmonicInteriorKernelXGradientConstant_nonneg
  positivity

end CKN.Foundation.Heat
