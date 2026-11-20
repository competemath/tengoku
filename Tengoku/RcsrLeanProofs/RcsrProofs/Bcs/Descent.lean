/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Metric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent and positivity

Every state other than the base has a neighbor whose distance value is exactly
one smaller (`descent_*`), the distance is nonnegative, and it vanishes only at
the base state. Together with the Lipschitz bounds these facts characterize
`D` as the graph distance.
-/

namespace Bcs

set_option maxHeartbeats 8000000 in
theorem descent_1 (x y z : Int) (h : ¬(x = 0 ∧ y = 0 ∧ z = 0)) :
    D2 x y z = D1 x y z - 1 ∨
      D2 x y (z+1) = D1 x y z - 1 ∨
      D3 x y z = D1 x y z - 1 ∨
      D3 x (y+1) z = D1 x y z - 1 ∨
      D4 x y z = D1 x y z - 1 ∨
      D4 (x+1) y z = D1 x y z - 1 := by
  unfold D1 D2 D3 D4
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_2 (x y z : Int) :
    D1 x y z = D2 x y z - 1 ∨
      D1 x y (z-1) = D2 x y z - 1 ∨
      D5 (x-1) (y-1) (z+1) = D2 x y z - 1 ∨
      D5 x y z = D2 x y z - 1 ∨
      D6 x y z = D2 x y z - 1 ∨
      D6 x (y+1) z = D2 x y z - 1 := by
  unfold D1 D2 D5 D6
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_3 (x y z : Int) :
    D1 x y z = D3 x y z - 1 ∨
      D1 x (y-1) z = D3 x y z - 1 ∨
      D5 (x-1) (y-1) (z+1) = D3 x y z - 1 ∨
      D5 x (y-1) (z+1) = D3 x y z - 1 ∨
      D7 (x-1) (y-1) (z+1) = D3 x y z - 1 ∨
      D7 x y z = D3 x y z - 1 := by
  unfold D1 D3 D5 D7
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_4 (x y z : Int) :
    D1 x y z = D4 x y z - 1 ∨
      D1 (x-1) y z = D4 x y z - 1 ∨
      D6 (x-1) y (z+1) = D4 x y z - 1 ∨
      D6 x (y+1) z = D4 x y z - 1 ∨
      D7 (x-1) y z = D4 x y z - 1 ∨
      D7 (x-1) y (z+1) = D4 x y z - 1 := by
  unfold D1 D4 D6 D7
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_5 (x y z : Int) :
    D2 (x+1) (y+1) (z-1) = D5 x y z - 1 ∨
      D2 x y z = D5 x y z - 1 ∨
      D3 (x+1) (y+1) (z-1) = D5 x y z - 1 ∨
      D3 x (y+1) (z-1) = D5 x y z - 1 ∨
      D8 x y z = D5 x y z - 1 ∨
      D8 x y (z+1) = D5 x y z - 1 := by
  unfold D2 D3 D5 D8
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_6 (x y z : Int) :
    D2 x y z = D6 x y z - 1 ∨
      D2 x (y-1) z = D6 x y z - 1 ∨
      D4 (x+1) y (z-1) = D6 x y z - 1 ∨
      D4 x (y-1) z = D6 x y z - 1 ∨
      D8 (x-1) (y-1) (z+1) = D6 x y z - 1 ∨
      D8 x (y-1) (z+1) = D6 x y z - 1 := by
  unfold D2 D4 D6 D8
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_7 (x y z : Int) :
    D3 (x+1) (y+1) (z-1) = D7 x y z - 1 ∨
      D3 x y z = D7 x y z - 1 ∨
      D4 (x+1) y z = D7 x y z - 1 ∨
      D4 (x+1) y (z-1) = D7 x y z - 1 ∨
      D8 x (y-1) (z+1) = D7 x y z - 1 ∨
      D8 x y (z+1) = D7 x y z - 1 := by
  unfold D3 D4 D7 D8
  split <;> omega

set_option maxHeartbeats 8000000 in
theorem descent_8 (x y z : Int) :
    D5 x y z = D8 x y z - 1 ∨
      D5 x y (z-1) = D8 x y z - 1 ∨
      D6 (x+1) (y+1) (z-1) = D8 x y z - 1 ∨
      D6 x (y+1) (z-1) = D8 x y z - 1 ∨
      D7 x (y+1) (z-1) = D8 x y z - 1 ∨
      D7 x y (z-1) = D8 x y z - 1 := by
  unfold D5 D6 D7 D8
  split <;> omega

theorem d1_zero_iff (x y z : Int) : D1 x y z = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 := by
  unfold D1; split <;> omega

theorem d2_pos (x y z : Int) : 1 ≤ D2 x y z := by
  unfold D2; omega

theorem d3_pos (x y z : Int) : 1 ≤ D3 x y z := by
  unfold D3; omega

theorem d4_pos (x y z : Int) : 1 ≤ D4 x y z := by
  unfold D4; omega

theorem d5_pos (x y z : Int) : 1 ≤ D5 x y z := by
  unfold D5; omega

theorem d6_pos (x y z : Int) : 1 ≤ D6 x y z := by
  unfold D6; omega

theorem d7_pos (x y z : Int) : 1 ≤ D7 x y z := by
  unfold D7; omega

theorem d8_pos (x y z : Int) : 1 ≤ D8 x y z := by
  unfold D8; split <;> omega

theorem d1_nonneg (x y z : Int) : 0 ≤ D1 x y z := by
  unfold D1; split <;> omega

end Bcs
