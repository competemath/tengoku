/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceMorrey

/-!
# Source Morrey Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The slicewise interface for the divergence-form pressure source carrying a
spatial cutoff.  These bounds are source estimates only; they do not select a
weak pressure gradient or prove its spacetime pairing. -/

/-- Cutoff pressure-Poisson source used to estimate the selected gradient in Morrey spaces. -/
def sourceMorreyCutoffV
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3) : Vec3 → Vec3 :=
  pressureDivergenceCutoffSource η dη u Du f

end CKN.Core.Step4
