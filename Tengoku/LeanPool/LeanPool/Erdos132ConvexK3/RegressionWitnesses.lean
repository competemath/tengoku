/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos132ConvexK3.Basic
public import Tengoku

/-!
# Exact rational regression witnesses

Kernel-reduced checks for the three configurations used during the convex
`k = 3` campaign.  Keeping them at the basic layer lets global counterexample
regressions use them without importing the closure stack.
-/

@[expose] public section

namespace LeanPool.Erdos132ConvexK3.Witnesses

open LeanPool.Erdos132ConvexK3

/-- Attempt 2's exact integer heptagon, in positive cyclic order. -/
def heptagon : Fin 7 → Point ℚ :=
  ![(0, 0), (72, 0), (45, 68), (40, 75), (36, 77), (32, 75), (27, 68)]

/--
@isnad1 id=cyclicst.0h0v.s3.ebee814e4d92 from=translated src=- shape=0792f4bc vocab=794a17d2
-/
theorem heptagon_strict_convex : CyclicStrictConvex heptagon := by
  unfold CyclicStrictConvex
  decide +kernel

/--
@isnad1 id=hastopth.0h0v.s4.ca85a43c530e from=translated src=- shape=37aeb9eb vocab=22d61c45
-/
theorem heptagon_top_three :
    HasTopThreeDistanceClasses heptagon 7225 6649 5353 := by
  unfold HasTopThreeDistanceClasses
  decide +kernel

/--
@isnad1 id=and.0h0v.s8.fe38d10280ec from=translated src=- shape=e378ab77 vocab=d45737e4
-/
theorem heptagon_double_ladder :
    sqDist (heptagon 0) (heptagon 6) = 5353 ∧
    sqDist (heptagon 0) (heptagon 5) = 6649 ∧
    sqDist (heptagon 0) (heptagon 4) = 7225 ∧
    sqDist (heptagon 1) (heptagon 2) = 5353 ∧
    sqDist (heptagon 1) (heptagon 3) = 6649 ∧
    sqDist (heptagon 1) (heptagon 4) = 7225 := by
  decide +kernel

/--
@isnad1 id=eq.0h0v.s5.6a81c1cb09a2 from=translated src=- shape=71534465 vocab=0fabebed
-/
theorem heptagon_x_degree : vertexDegree heptagon 7225 6649 5353 0 = 5 := by
  decide +kernel

/-- Attempt 3's exact nine-point low-altitude insertion witness. -/
def ninePoint : Fin 9 → Point ℚ :=
  ![(0, 0), (180, -1), (370, -1), (570, 0), (309, 862),
    (300, 875), (285, 880), (270, 875), (261, 862)]

/--
@isnad1 id=cyclicst.0h0v.s3.6906e790826a from=translated src=- shape=0792f4bc vocab=d95530ef
-/
theorem ninePoint_strict_convex : CyclicStrictConvex ninePoint := by
  unfold CyclicStrictConvex
  decide +kernel

/--
@isnad1 id=hastopth.0h0v.s4.ac96807a64c7 from=translated src=- shape=37aeb9eb vocab=c3a32d21
-/
theorem ninePoint_top_three :
    HasTopThreeDistanceClasses ninePoint 855625 838525 811165 := by
  unfold HasTopThreeDistanceClasses
  decide +kernel

/--
@isnad1 id=and.0h0v.s6.ce42288e782b from=translated src=- shape=e14c2546 vocab=af8e03e6
-/
theorem ninePoint_insertions_isolated :
    vertexDegree ninePoint 855625 838525 811165 1 = 0 ∧
      vertexDegree ninePoint 855625 838525 811165 2 = 0 := by
  decide +kernel

/-- A second exact rational hexagon, in positive cyclic order. -/
def rationalHexagon : Fin 6 → Point ℚ :=
  ![(0, -20),
    (24171 / 50380, -(12571661 / 629750)),
    (48331 / 50380, -(12546661 / 629750)),
    (1208 / 229, -(4480 / 229)),
    (1, 0),
    (-1, 0)]

/--
@isnad1 id=cyclicst.0h0v.s3.937e8ef45463 from=translated src=- shape=0792f4bc vocab=ff283e8e
-/
theorem rationalHexagon_strict_convex : CyclicStrictConvex rationalHexagon := by
  unfold CyclicStrictConvex
  decide +kernel

/--
@isnad1 id=hastopth.0h0v.s5.d24e59aa12e6 from=translated src=- shape=33fae45c vocab=94b0ad7d
-/
theorem rationalHexagon_top_three :
    HasTopThreeDistanceClasses rationalHexagon
      (96661 / 229) 401 (2776265163521 / 6927250000) := by
  unfold HasTopThreeDistanceClasses
  decide +kernel

/--
@isnad1 id=and.0h0v.s8.65252ecd3483 from=translated src=- shape=08123f2c vocab=bc491d4d
-/
theorem rationalHexagon_key_edges :
    sqDist (rationalHexagon 3) (rationalHexagon 5) = 96661 / 229 ∧
    sqDist (rationalHexagon 0) (rationalHexagon 5) = 401 ∧
    sqDist (rationalHexagon 3) (rationalHexagon 4) = 401 ∧
    sqDist (rationalHexagon 0) (rationalHexagon 4) = 401 ∧
    sqDist (rationalHexagon 2) (rationalHexagon 5) =
      2776265163521 / 6927250000 := by
  decide +kernel

/--
@isnad1 id=and.0h0v.s7.11f12e677c30 from=translated src=- shape=cf0b767e vocab=8037fb6f
-/
theorem rationalHexagon_lower_degrees :
    vertexDegree rationalHexagon
        (96661 / 229) 401 (2776265163521 / 6927250000) 1 = 0 ∧
      vertexDegree rationalHexagon
        (96661 / 229) 401 (2776265163521 / 6927250000) 2 = 1 := by
  decide +kernel

end LeanPool.Erdos132ConvexK3.Witnesses
