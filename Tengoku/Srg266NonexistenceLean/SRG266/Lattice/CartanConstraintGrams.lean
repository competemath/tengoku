/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanADualMinimum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem gramA_two_det : (gramA 2).det = 3 := by decide

set_option maxRecDepth 8192 in
theorem gramA_five_det : (gramA 5).det = 6 := by decide

theorem cartanA_two_nondegenerate : (cartanARatForm 2).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  change ((gramA 2).map (fun z : ℤ => (z : ℚ))).det ≠ 0
  rw [← Int.cast_det, gramA_two_det]
  norm_num

theorem cartanA_five_nondegenerate : (cartanARatForm 5).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  change ((gramA 5).map (fun z : ℤ => (z : ℚ))).det ≠ 0
  rw [← Int.cast_det, gramA_five_det]
  norm_num

end SRG266.Lattice
