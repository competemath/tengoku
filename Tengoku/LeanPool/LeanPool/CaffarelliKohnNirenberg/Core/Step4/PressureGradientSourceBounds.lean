/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyData
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.HolderTripleProducts

/-!
# Pressure Gradient Source Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- The product-rule source obtained after inserting a spatial cutoff into the
quadratic tensor.  The field `dη j` is the j-th spatial derivative of the
cutoff; its analytic derivative estimate is passed at the use site. -/
def pressureDivergenceCutoffSource
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3) : Vec3 → Vec3 :=
  fun x i => ∑ j, (η x * Du x i j * u x j + dη j x * u x i * u x j) - η x * f x i

/-! A cutoff does not change the product exponents.  The two cutoff bounds
are kept as separate parameters so that the spatial derivative contribution
can be instantiated with `C₁₀ / ρ`. -/

end CKN.Core.Step4
