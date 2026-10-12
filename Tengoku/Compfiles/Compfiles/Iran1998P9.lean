/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# Iranian Mathematical Olympiad 1998, Problem 9

Let x,y,z > 1 and 1/x + 1/y + 1/z = 2. Prove that

  √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).

-/

namespace Iran1998P9

/--
@isnad1 id=eq.0h1v.s7.45bf10405bbf from=translated src=- shape=9b83e5ad vocab=d392b7d7
-/
lemma compute_norm (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖ = Real.sqrt (∑i : Fin 3, (v i)^2) := by
  simp [EuclideanSpace.norm_eq v]

end Iran1998P9
