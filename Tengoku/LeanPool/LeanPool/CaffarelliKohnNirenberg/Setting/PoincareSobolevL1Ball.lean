/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1

/-!
# Poincare Sobolev L1 Ball

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace CKN

noncomputable section

/-- Translation and dilation map transporting unit-ball inequalities to arbitrary balls. -/
def euclideanAffineMap (x₀ : Vec 3) (r : ℝ) (x : Vec 3) : Vec 3 :=
  x₀ + r • x

end
end CKN
