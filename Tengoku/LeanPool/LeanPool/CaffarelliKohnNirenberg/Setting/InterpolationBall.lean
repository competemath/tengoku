/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.H1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import Tengoku

/-!
# Interpolation Ball

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN

/-- Interpolation weight relating the velocity exponent to the L² and L⁶ endpoints. -/
def interpolationTheta (q : ℝ) : ℝ :=
  3 * (q - 2) / (2 * q)

/-- Exponent of the gradient contribution in the velocity interpolation estimate. -/
def interpolationExponent (q : ℝ) : ℝ :=
  3 * (q - 2) / 4

/-! The witness supplied by the Sobolev bridge is finite.  Keeping this fact
separate lets cylinder arguments pass from `ℝ≥0∞` estimates to the real
scale quantities without introducing an artificial finiteness hypothesis. -/

end CKN
