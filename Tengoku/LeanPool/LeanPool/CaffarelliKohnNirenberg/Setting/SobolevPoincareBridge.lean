/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Tengoku

/-!
# Sobolev Poincare Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Volume-normalization coefficient for the full ball Sobolev estimate. -/
noncomputable def sobolevPoincareBallFullConstant : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi * 4 / 3) ^ (-(1 / 3 : ℝ))

end CKN
