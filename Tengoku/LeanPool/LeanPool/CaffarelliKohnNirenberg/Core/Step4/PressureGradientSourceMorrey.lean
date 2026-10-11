/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceBounds

/-!
# Pressure Gradient Source Morrey

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The source estimate on a spacetime carrier.  The two product exponents
combine to `(1 / τ + 8 / 25)⁻¹`; the force is lowered from its q-Morrey
exponent only after the common target exponent has been selected. -/

end CKN.Core.Step4
