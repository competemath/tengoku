/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import Tengoku.Seed.Analysis.Convolution
public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Indicator
public import Tengoku.Seed.MeasureTheory.Integral.MeanInequalities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Newtonian Derivative Local Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The scalar convolution convention used for the Newtonian derivative. -/
def scalarConvolution (f g : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y : Vec3, f y * g (x - y)

/-- Extended nonnegative convolution used to majorize ordinary convolution integrals. -/
def convolutionMajorant (f g : Vec3 → ℝ≥0∞) (x : Vec3) : ℝ≥0∞ :=
  ∫⁻ y : Vec3, f y * g (x - y)

/-! The next declarations specialize the preceding Young estimate to the
three-dimensional Newtonian derivative. -/

/-- The Newtonian derivative kernel truncated to a ball about the origin. -/
def truncatedNewtonianDerivative (R : ℝ) (i : Fin 3) : Vec3 → ℝ := fun z =>
  if ‖z‖ < R then spatialDeriv newtonianKernel i z else 0

/-- The truncated Newtonian derivative kernel is measurable. -/
theorem measurable_truncatedNewtonianDerivative (R : ℝ) (i : Fin 3) :
    Measurable (truncatedNewtonianDerivative R i) := by
  exact (measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)).piecewise
    (measurableSet_lt measurable_norm measurable_const) measurable_const

/-! The complementary kernel is kept separate so that the local estimate can
be assembled from a Young bound and a pointwise tail bound. -/

/-- The Newtonian derivative kernel restricted to the complement of a ball. -/
def farNewtonianDerivative (R : ℝ) (i : Fin 3) : Vec3 → ℝ := fun z =>
  if R ≤ ‖z‖ then spatialDeriv newtonianKernel i z else 0

/-- The complementary Newtonian derivative kernel is measurable. -/
theorem measurable_farNewtonianDerivative (R : ℝ) (i : Fin 3) :
    Measurable (farNewtonianDerivative R i) := by
  exact (measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)).piecewise
    (measurableSet_le measurable_const measurable_norm) measurable_const

/-- The first Newtonian derivative potential, with the derivative in the kernel slot. -/
def newtonianDerivativePotential (i : Fin 3) (G : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y, spatialDeriv newtonianKernel i (x - y) * G y

end CKN.Foundation.Euclidean
