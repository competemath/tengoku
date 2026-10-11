/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm

/-!
# Poincare Sobolev L1 Vec

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-- Explicit constant for the vector-valued ball inequality. -/
noncomputable def poincareSobolevL1VectorConstant : ℝ :=
  2 * Real.sqrt 3 * poincareSobolevL1Constant.toReal

end
end CKN
