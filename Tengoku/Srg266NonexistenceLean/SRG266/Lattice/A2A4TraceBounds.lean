/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanFrameTraceBounds
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.OrthogonalIndependentSum
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SmallCartanDeterminants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=nondegen.0h0v.s5.9000c3c2b4db from=translated src=- shape=403153e1 vocab=7569c3cb
-/
theorem cartanA_four_nondegenerate : (cartanARatForm 4).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  change ((gramA 4).map (fun z : ℤ => (z : ℚ))).det ≠ 0
  rw [← Int.cast_det, gramA_four_det]
  norm_num

end SRG266.Lattice
