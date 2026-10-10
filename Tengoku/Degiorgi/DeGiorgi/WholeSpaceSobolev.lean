import Tengoku.Degiorgi.DeGiorgi.Common

/-!
# Chapter 02: Whole-Space Sobolev

This module develops the whole-space Sobolev inequality used later in the local
iteration arguments.

The main export is `DeGiorgi.sobolev_of_approx`.
-/

noncomputable section

open MeasureTheory Metric Filter Set Function
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Section 1: Sobolev Constant -/

/-- The Sobolev constant for the general `W^{1,p} -> L^{p*}` embedding,
extracted from Mathlib. -/
noncomputable def C_gns (d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  (MeasureTheory.SNormLESNormFDerivOfEqConst (F := ℝ)
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) p : ℝ≥0)

/-! ## Section 2: Exponent Arithmetic -/

/-! ## Section 3: GNS for Smooth Compactly Supported Functions -/

/-! ## Section 4: Gradient norm comparison -/

/-! ## Section 5: Extension to `W₀^{1,p}` by Fatou -/

end DeGiorgi
