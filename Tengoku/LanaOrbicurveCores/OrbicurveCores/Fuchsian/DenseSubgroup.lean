/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Non-discrete subgroups of `SL(2, ℝ)` containing unipotent directions

Elementary replacement for the Lie-algebra argument "a closed non-discrete subgroup normalised by
a Zariski-dense group is everything", specialised to `SL(2, ℝ)`.

* `SL2R.uU t = [[1, t], [0, 1]]`, `SL2R.uL t = [[1, 0], [t, 1]]`.
* `SL2R.eq_top_of_unipotents`: a subgroup containing all `uU t` and `uL t` is `⊤`
  (every matrix is a product of at most four elementary matrices).
* `SL2R.uU_mem_of_tendsto`: a **closed** subgroup `K` containing `D = diag(l, l⁻¹)` (`l > 1`) and
  a sequence `gₙ → 1` with nonzero upper-right entries contains every `uU t`. Conjugating by
  powers of `D` rescales the upper-right entry to a fixed size, and a limit point lies in `K`.
-/

open Matrix Filter Topology
open scoped MatrixGroups

namespace OrbicurveCores.SL2R

/-- The upper unipotent `[[1, t], [0, 1]]`. -/
def uU (t : ℝ) : SL(2, ℝ) := ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

/-- The lower unipotent `[[1, 0], [t, 1]]`. -/
def uL (t : ℝ) : SL(2, ℝ) := ⟨!![1, 0; t, 1], by simp [det_fin_two]⟩

@[simp] lemma coe_uU (t : ℝ) : ((uU t : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] :=
  rfl

@[simp] lemma coe_uL (t : ℝ) : ((uL t : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; t, 1] :=
  rfl

/-- The element `S = [[0, -1], [1, 0]]` of `SL(2, ℝ)`. -/
def wS : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

end OrbicurveCores.SL2R
