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
/--
@isnad1 id=or.1h3v.s7.169aa6d59a4a from=translated src=- shape=fe3f326d vocab=89e74d7d
-/
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
/--
@isnad1 id=or.0h3v.s7.7beadcfef65b from=translated src=- shape=72688066 vocab=85ce8e3b
-/
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
/--
@isnad1 id=or.0h3v.s7.36f7f5f09b8d from=translated src=- shape=659def5e vocab=d6c9d020
-/
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
/--
@isnad1 id=or.0h3v.s7.d26d06e3ec55 from=translated src=- shape=d60ad9a0 vocab=eb6da420
-/
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
/--
@isnad1 id=or.0h3v.s7.48823b89d3f3 from=translated src=- shape=7526c469 vocab=dc441210
-/
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
/--
@isnad1 id=or.0h3v.s7.45aaf98d6829 from=translated src=- shape=dbd2257e vocab=47a02c85
-/
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
/--
@isnad1 id=or.0h3v.s7.ae8951be9a59 from=translated src=- shape=126e90c9 vocab=e6135aaa
-/
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
/--
@isnad1 id=or.0h3v.s7.518f8435f54a from=translated src=- shape=f69aadbf vocab=1a511458
-/
theorem descent_8 (x y z : Int) :
    D5 x y z = D8 x y z - 1 ∨
      D5 x y (z-1) = D8 x y z - 1 ∨
      D6 (x+1) (y+1) (z-1) = D8 x y z - 1 ∨
      D6 x (y+1) (z-1) = D8 x y z - 1 ∨
      D7 x (y+1) (z-1) = D8 x y z - 1 ∨
      D7 x y (z-1) = D8 x y z - 1 := by
  unfold D5 D6 D7 D8
  split <;> omega

/--
@isnad1 id=iff.0h3v.s5.7504f2d94b95 from=translated src=- shape=568fdcdd vocab=22980c76
-/
theorem d1_zero_iff (x y z : Int) : D1 x y z = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 := by
  unfold D1; split <;> omega

/--
@isnad1 id=le.0h3v.s4.d2cbfa102fa4 from=translated src=- shape=ac9c39a3 vocab=5774265d
-/
theorem d2_pos (x y z : Int) : 1 ≤ D2 x y z := by
  unfold D2; omega

/--
@isnad1 id=le.0h3v.s4.ce03e2f1e18d from=translated src=- shape=ac9c39a3 vocab=417ed19b
-/
theorem d3_pos (x y z : Int) : 1 ≤ D3 x y z := by
  unfold D3; omega

/--
@isnad1 id=le.0h3v.s4.24977a02f108 from=translated src=- shape=ac9c39a3 vocab=38275e1f
-/
theorem d4_pos (x y z : Int) : 1 ≤ D4 x y z := by
  unfold D4; omega

/--
@isnad1 id=le.0h3v.s4.85be9ecc968b from=translated src=- shape=ac9c39a3 vocab=9f752c66
-/
theorem d5_pos (x y z : Int) : 1 ≤ D5 x y z := by
  unfold D5; omega

/--
@isnad1 id=le.0h3v.s4.6d59205b4463 from=translated src=- shape=ac9c39a3 vocab=43cde791
-/
theorem d6_pos (x y z : Int) : 1 ≤ D6 x y z := by
  unfold D6; omega

/--
@isnad1 id=le.0h3v.s4.729027224756 from=translated src=- shape=ac9c39a3 vocab=ec17f8a5
-/
theorem d7_pos (x y z : Int) : 1 ≤ D7 x y z := by
  unfold D7; omega

/--
@isnad1 id=le.0h3v.s4.e12a41b4de0b from=translated src=- shape=ac9c39a3 vocab=c5a3fb66
-/
theorem d8_pos (x y z : Int) : 1 ≤ D8 x y z := by
  unfold D8; split <;> omega

/--
@isnad1 id=le.0h3v.s4.dcfb4ac4a917 from=translated src=- shape=ac9c39a3 vocab=f958ccac
-/
theorem d1_nonneg (x y z : Int) : 0 ≤ D1 x y z := by
  unfold D1; split <;> omega

end Bcs
