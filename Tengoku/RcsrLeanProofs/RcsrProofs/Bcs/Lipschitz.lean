/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Metric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Per-edge Lipschitz bounds

For each of the 24 voltage edges (u,v,δ) of the bcs quotient graph, the distance
functions of the two endpoint classes differ by exactly 1 across the edge:
`D_v (p+δ) - D_u p = ±1`. (Both traversal directions are the same statement.)
Each proof is a case split on the exceptional-line corrections followed by
linear integer arithmetic.
-/

namespace Bcs

theorem lip_e0_12 (x y z : Int) :
    D2 x y z - D1 x y z = 1 ∨ D2 x y z - D1 x y z = -1 := by
  unfold D1 D2
  split <;> omega

theorem lip_e1_12 (x y z : Int) :
    D2 x y (z+1) - D1 x y z = 1 ∨ D2 x y (z+1) - D1 x y z = -1 := by
  unfold D1 D2
  split <;> omega

theorem lip_e2_13 (x y z : Int) :
    D3 x y z - D1 x y z = 1 ∨ D3 x y z - D1 x y z = -1 := by
  unfold D1 D3
  split <;> omega

theorem lip_e3_13 (x y z : Int) :
    D3 x (y+1) z - D1 x y z = 1 ∨ D3 x (y+1) z - D1 x y z = -1 := by
  unfold D1 D3
  split <;> omega

theorem lip_e4_14 (x y z : Int) :
    D4 x y z - D1 x y z = 1 ∨ D4 x y z - D1 x y z = -1 := by
  unfold D1 D4
  split <;> omega

theorem lip_e5_14 (x y z : Int) :
    D4 (x+1) y z - D1 x y z = 1 ∨ D4 (x+1) y z - D1 x y z = -1 := by
  unfold D1 D4
  split <;> omega

theorem lip_e6_25 (x y z : Int) :
    D5 (x-1) (y-1) (z+1) - D2 x y z = 1 ∨ D5 (x-1) (y-1) (z+1) - D2 x y z = -1 := by
  unfold D2 D5
  omega

theorem lip_e7_25 (x y z : Int) :
    D5 x y z - D2 x y z = 1 ∨ D5 x y z - D2 x y z = -1 := by
  unfold D2 D5
  omega

theorem lip_e8_26 (x y z : Int) :
    D6 x y z - D2 x y z = 1 ∨ D6 x y z - D2 x y z = -1 := by
  unfold D2 D6
  omega

theorem lip_e9_26 (x y z : Int) :
    D6 x (y+1) z - D2 x y z = 1 ∨ D6 x (y+1) z - D2 x y z = -1 := by
  unfold D2 D6
  omega

theorem lip_e10_35 (x y z : Int) :
    D5 (x-1) (y-1) (z+1) - D3 x y z = 1 ∨ D5 (x-1) (y-1) (z+1) - D3 x y z = -1 := by
  unfold D3 D5
  omega

theorem lip_e11_35 (x y z : Int) :
    D5 x (y-1) (z+1) - D3 x y z = 1 ∨ D5 x (y-1) (z+1) - D3 x y z = -1 := by
  unfold D3 D5
  omega

theorem lip_e12_37 (x y z : Int) :
    D7 (x-1) (y-1) (z+1) - D3 x y z = 1 ∨ D7 (x-1) (y-1) (z+1) - D3 x y z = -1 := by
  unfold D3 D7
  omega

theorem lip_e13_37 (x y z : Int) :
    D7 x y z - D3 x y z = 1 ∨ D7 x y z - D3 x y z = -1 := by
  unfold D3 D7
  omega

theorem lip_e14_46 (x y z : Int) :
    D6 (x-1) y (z+1) - D4 x y z = 1 ∨ D6 (x-1) y (z+1) - D4 x y z = -1 := by
  unfold D4 D6
  omega

theorem lip_e15_46 (x y z : Int) :
    D6 x (y+1) z - D4 x y z = 1 ∨ D6 x (y+1) z - D4 x y z = -1 := by
  unfold D4 D6
  omega

theorem lip_e16_47 (x y z : Int) :
    D7 (x-1) y z - D4 x y z = 1 ∨ D7 (x-1) y z - D4 x y z = -1 := by
  unfold D4 D7
  omega

theorem lip_e17_47 (x y z : Int) :
    D7 (x-1) y (z+1) - D4 x y z = 1 ∨ D7 (x-1) y (z+1) - D4 x y z = -1 := by
  unfold D4 D7
  omega

theorem lip_e18_58 (x y z : Int) :
    D8 x y z - D5 x y z = 1 ∨ D8 x y z - D5 x y z = -1 := by
  unfold D5 D8
  split <;> omega

theorem lip_e19_58 (x y z : Int) :
    D8 x y (z+1) - D5 x y z = 1 ∨ D8 x y (z+1) - D5 x y z = -1 := by
  unfold D5 D8
  split <;> omega

theorem lip_e20_68 (x y z : Int) :
    D8 (x-1) (y-1) (z+1) - D6 x y z = 1 ∨ D8 (x-1) (y-1) (z+1) - D6 x y z = -1 := by
  unfold D6 D8
  split <;> omega

theorem lip_e21_68 (x y z : Int) :
    D8 x (y-1) (z+1) - D6 x y z = 1 ∨ D8 x (y-1) (z+1) - D6 x y z = -1 := by
  unfold D6 D8
  split <;> omega

theorem lip_e22_78 (x y z : Int) :
    D8 x (y-1) (z+1) - D7 x y z = 1 ∨ D8 x (y-1) (z+1) - D7 x y z = -1 := by
  unfold D7 D8
  split <;> omega

theorem lip_e23_78 (x y z : Int) :
    D8 x y (z+1) - D7 x y z = 1 ∨ D8 x y (z+1) - D7 x y z = -1 := by
  unfold D7 D8
  split <;> omega

end Bcs
