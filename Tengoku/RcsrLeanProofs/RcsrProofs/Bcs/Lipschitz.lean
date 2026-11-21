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

/--
@isnad1 id=or.0h3v.s5.3df94fc092c3 from=translated src=- shape=f932467b vocab=8da7255b
-/
theorem lip_e0_12 (x y z : Int) :
    D2 x y z - D1 x y z = 1 ∨ D2 x y z - D1 x y z = -1 := by
  unfold D1 D2
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.870560c73ca7 from=translated src=- shape=1b1208ff vocab=e1a3636f
-/
theorem lip_e1_12 (x y z : Int) :
    D2 x y (z+1) - D1 x y z = 1 ∨ D2 x y (z+1) - D1 x y z = -1 := by
  unfold D1 D2
  split <;> omega

/--
@isnad1 id=or.0h3v.s5.6133a6f89929 from=translated src=- shape=f932467b vocab=13423b99
-/
theorem lip_e2_13 (x y z : Int) :
    D3 x y z - D1 x y z = 1 ∨ D3 x y z - D1 x y z = -1 := by
  unfold D1 D3
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.842b97683466 from=translated src=- shape=738c161e vocab=396d9953
-/
theorem lip_e3_13 (x y z : Int) :
    D3 x (y+1) z - D1 x y z = 1 ∨ D3 x (y+1) z - D1 x y z = -1 := by
  unfold D1 D3
  split <;> omega

/--
@isnad1 id=or.0h3v.s5.030c02aaeea4 from=translated src=- shape=f932467b vocab=471635f3
-/
theorem lip_e4_14 (x y z : Int) :
    D4 x y z - D1 x y z = 1 ∨ D4 x y z - D1 x y z = -1 := by
  unfold D1 D4
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.d663317c9ffa from=translated src=- shape=91ace023 vocab=2f8e7f40
-/
theorem lip_e5_14 (x y z : Int) :
    D4 (x+1) y z - D1 x y z = 1 ∨ D4 (x+1) y z - D1 x y z = -1 := by
  unfold D1 D4
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.4739834957fd from=translated src=- shape=06298967 vocab=142e4e21
-/
theorem lip_e6_25 (x y z : Int) :
    D5 (x-1) (y-1) (z+1) - D2 x y z = 1 ∨ D5 (x-1) (y-1) (z+1) - D2 x y z = -1 := by
  unfold D2 D5
  omega

/--
@isnad1 id=or.0h3v.s5.2dfe5b2ea679 from=translated src=- shape=f932467b vocab=8133a742
-/
theorem lip_e7_25 (x y z : Int) :
    D5 x y z - D2 x y z = 1 ∨ D5 x y z - D2 x y z = -1 := by
  unfold D2 D5
  omega

/--
@isnad1 id=or.0h3v.s5.653897c2a9bd from=translated src=- shape=f932467b vocab=569307ac
-/
theorem lip_e8_26 (x y z : Int) :
    D6 x y z - D2 x y z = 1 ∨ D6 x y z - D2 x y z = -1 := by
  unfold D2 D6
  omega

/--
@isnad1 id=or.0h3v.s6.dd3efde9fe4b from=translated src=- shape=738c161e vocab=07c7fcf6
-/
theorem lip_e9_26 (x y z : Int) :
    D6 x (y+1) z - D2 x y z = 1 ∨ D6 x (y+1) z - D2 x y z = -1 := by
  unfold D2 D6
  omega

/--
@isnad1 id=or.0h3v.s6.d5088cbe2b7f from=translated src=- shape=06298967 vocab=473429cf
-/
theorem lip_e10_35 (x y z : Int) :
    D5 (x-1) (y-1) (z+1) - D3 x y z = 1 ∨ D5 (x-1) (y-1) (z+1) - D3 x y z = -1 := by
  unfold D3 D5
  omega

/--
@isnad1 id=or.0h3v.s6.3007071976d9 from=translated src=- shape=378cc4c7 vocab=473429cf
-/
theorem lip_e11_35 (x y z : Int) :
    D5 x (y-1) (z+1) - D3 x y z = 1 ∨ D5 x (y-1) (z+1) - D3 x y z = -1 := by
  unfold D3 D5
  omega

/--
@isnad1 id=or.0h3v.s6.35605819ce9b from=translated src=- shape=06298967 vocab=e06fcc94
-/
theorem lip_e12_37 (x y z : Int) :
    D7 (x-1) (y-1) (z+1) - D3 x y z = 1 ∨ D7 (x-1) (y-1) (z+1) - D3 x y z = -1 := by
  unfold D3 D7
  omega

/--
@isnad1 id=or.0h3v.s5.69c81d191f54 from=translated src=- shape=f932467b vocab=256cd1a2
-/
theorem lip_e13_37 (x y z : Int) :
    D7 x y z - D3 x y z = 1 ∨ D7 x y z - D3 x y z = -1 := by
  unfold D3 D7
  omega

/--
@isnad1 id=or.0h3v.s6.78d78b34440b from=translated src=- shape=89ac7b22 vocab=1ef7b9aa
-/
theorem lip_e14_46 (x y z : Int) :
    D6 (x-1) y (z+1) - D4 x y z = 1 ∨ D6 (x-1) y (z+1) - D4 x y z = -1 := by
  unfold D4 D6
  omega

/--
@isnad1 id=or.0h3v.s6.d4d12e6cd831 from=translated src=- shape=738c161e vocab=1ef7b9aa
-/
theorem lip_e15_46 (x y z : Int) :
    D6 x (y+1) z - D4 x y z = 1 ∨ D6 x (y+1) z - D4 x y z = -1 := by
  unfold D4 D6
  omega

/--
@isnad1 id=or.0h3v.s6.4f7151eea161 from=translated src=- shape=86e5782e vocab=026d0df9
-/
theorem lip_e16_47 (x y z : Int) :
    D7 (x-1) y z - D4 x y z = 1 ∨ D7 (x-1) y z - D4 x y z = -1 := by
  unfold D4 D7
  omega

/--
@isnad1 id=or.0h3v.s6.62dc2dcd2f87 from=translated src=- shape=89ac7b22 vocab=4edc94c1
-/
theorem lip_e17_47 (x y z : Int) :
    D7 (x-1) y (z+1) - D4 x y z = 1 ∨ D7 (x-1) y (z+1) - D4 x y z = -1 := by
  unfold D4 D7
  omega

/--
@isnad1 id=or.0h3v.s5.cba824f1d0d0 from=translated src=- shape=f932467b vocab=7785b41e
-/
theorem lip_e18_58 (x y z : Int) :
    D8 x y z - D5 x y z = 1 ∨ D8 x y z - D5 x y z = -1 := by
  unfold D5 D8
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.1ef517e37699 from=translated src=- shape=1b1208ff vocab=fb26ecc6
-/
theorem lip_e19_58 (x y z : Int) :
    D8 x y (z+1) - D5 x y z = 1 ∨ D8 x y (z+1) - D5 x y z = -1 := by
  unfold D5 D8
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.03fc7318353e from=translated src=- shape=06298967 vocab=fb12c07d
-/
theorem lip_e20_68 (x y z : Int) :
    D8 (x-1) (y-1) (z+1) - D6 x y z = 1 ∨ D8 (x-1) (y-1) (z+1) - D6 x y z = -1 := by
  unfold D6 D8
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.2adbf64ed5a1 from=translated src=- shape=378cc4c7 vocab=fb12c07d
-/
theorem lip_e21_68 (x y z : Int) :
    D8 x (y-1) (z+1) - D6 x y z = 1 ∨ D8 x (y-1) (z+1) - D6 x y z = -1 := by
  unfold D6 D8
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.1c13d7759aa6 from=translated src=- shape=378cc4c7 vocab=63114151
-/
theorem lip_e22_78 (x y z : Int) :
    D8 x (y-1) (z+1) - D7 x y z = 1 ∨ D8 x (y-1) (z+1) - D7 x y z = -1 := by
  unfold D7 D8
  split <;> omega

/--
@isnad1 id=or.0h3v.s6.211893797265 from=translated src=- shape=1b1208ff vocab=63114151
-/
theorem lip_e23_78 (x y z : Int) :
    D8 x y (z+1) - D7 x y z = 1 ∨ D8 x y (z+1) - D7 x y z = -1 := by
  unfold D7 D8
  split <;> omega

end Bcs
