/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Internal

/-!
# Connectivity outside the isolated regions

After deleting one boundary edge of a region with at most two boundary
edges, its remaining boundary has size at most one. A simple path between
vertices outside that region cannot enter it and leave again: that would
repeat its sole boundary edge. Deleting the remaining boundary therefore
preserves reachability between outside vertices. This works for a whole
family simultaneously and supplies the core-connectivity invariant in
Monien and Preis's cycle-removal step.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

theorem mem_of_reachable_of_cut_empty {P : Finset V} (closed : B.cutFinset P = ∅)
    {u v : V} (reachable : B.Reachable u v) (member : u ∈ P) : v ∈ P := by
  obtain ⟨p⟩ := reachable
  induction p with
  | nil => exact member
  | @cons a b c adjacent p ih =>
    apply ih
    by_contra outside
    have crossing := B.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl ⟨member, outside⟩⟩
    rw [closed] at crossing
    exact Finset.notMem_empty _ crossing

theorem cut_card_le_one_after_chosen_deletion {ι : Type} (P : ι → Finset V)
    (chosen : ι → Sym2 V) (indices : Finset ι)
    (two : ∀ i ∈ indices, (B.cutFinset (P i)).card ≤ 2)
    (boundary : ∀ i ∈ indices, chosen i ∈ B.cutFinset (P i)) {i : ι} (hi : i ∈ indices) :
    ((B.deleteEdges (indices.image chosen : Set (Sym2 V))).cutFinset (P i)).card ≤ 1 := by
  rw [RedBlack.Internal.cut_deleteEdges]
  have subset : B.cutFinset (P i) \ indices.image chosen ⊆
      (B.cutFinset (P i)).erase (chosen i) := by
    intro e he
    obtain ⟨member, fresh⟩ := Finset.mem_sdiff.mp he
    apply Finset.mem_erase.mpr
    refine ⟨?_, member⟩
    rintro rfl
    exact fresh (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have count := Finset.card_erase_add_one (boundary i hi)
  have bound := Finset.card_le_card subset
  have := two i hi
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal
