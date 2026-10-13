/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Internal

/-!
# Preserving endpoint bags in graph induction

These operations implement the deletion cases of Fomin and Høie's Lemma 4
in *Pathwidth of cubic graphs and exact algorithms* (2006). A subset can be
appended as a new last bag. A deleted vertex can be restored when all its
neighbors occur in the last bag. All bounds count bag vertices, so a bound
`b` on nonempty bags corresponds to width at most `b - 1`. Without a terminal
neighbor condition, inserting the vertex into every bag costs at most one.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

/-- The one-bag decomposition ends in the full vertex set.
@isnad1 id=endsat.0h2v.s4.4e3d1f4a763d from=translated src=- shape=f362b934 vocab=d702be06
-/
theorem trivial_endsAt [Fintype W] : (trivial H).EndsAt Finset.univ := by
  refine ⟨⟨0, by simp [trivial]⟩, ?_, rfl⟩
  intro i
  have hi := i.isLt
  change i.val < 1 at hi
  change i.val ≤ 0
  lia

/-- Reversal turns a prescribed last bag into a prescribed first bag.
@isnad1 id=startsat.1h4v.s4.63aed949f5fc from=translated src=- shape=7a50af71 vocab=3520f012
-/
theorem EndsAt.reverse {D : PathDecomposition H} {X : Finset W}
    (hend : D.EndsAt X) : D.reverse.StartsAt X := by
  obtain ⟨last, hlast, hX⟩ := hend
  change ∃ first : Fin D.length, (∀ i, first ≤ i) ∧ D.bag first.rev = X
  refine ⟨last.rev, fun i => ?_, ?_⟩
  · simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr (hlast i.rev)
  · simpa only [Fin.rev_rev] using hX

/-- Reversal turns a prescribed first bag into a prescribed last bag.
@isnad1 id=endsat.1h4v.s4.da349dfee87c from=translated src=- shape=7a50af71 vocab=3520f012
-/
theorem StartsAt.reverse {D : PathDecomposition H} {X : Finset W}
    (hstart : D.StartsAt X) : D.reverse.EndsAt X := by
  obtain ⟨first, hfirst, hX⟩ := hstart
  change ∃ last : Fin D.length, (∀ i, i ≤ last) ∧ D.bag last.rev = X
  refine ⟨first.rev, fun i => ?_, ?_⟩
  · simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr (hfirst i.rev)
  · simpa only [Fin.rev_rev] using hX

/-- A decomposition with a first bag also has a last bag.
@isnad1 id=ex.1h4v.s4.8958dd2d1c80 from=translated src=- shape=4926ce80 vocab=1b482516
-/
theorem StartsAt.exists_endsAt {D : PathDecomposition H} {X : Finset W}
    (hstart : D.StartsAt X) : ∃ Y, D.EndsAt Y := by
  obtain ⟨first, _, _⟩ := hstart
  have hpos : 0 < D.length := lt_of_le_of_lt (Nat.zero_le _) first.isLt
  let last : Fin D.length := ⟨D.length - 1, by lia⟩
  refine ⟨D.bag last, last, ?_, rfl⟩
  intro i
  have hi := i.isLt
  change i.val ≤ D.length - 1
  lia

/-- Relabelling preserves the prescribed last bag.
@isnad1 id=endsat.1h7v.s5.84cd84d86f03 from=translated src=- shape=c469720d vocab=9f8b0377
-/
theorem EndsAt.relabel {V : Type} {G : SimpleGraph V} {D : PathDecomposition G}
    {X : Finset V} (hend : D.EndsAt X) (e : G ≃g H) :
    (D.relabel e).EndsAt (X.map e.toEquiv.toEmbedding) := by
  obtain ⟨last, hlast, hX⟩ := hend
  exact ⟨last, hlast, congrArg (Finset.map e.toEquiv.toEmbedding) hX⟩

/-- Relabelling preserves the prescribed first bag.
@isnad1 id=startsat.1h7v.s5.84488ee75ba3 from=translated src=- shape=c469720d vocab=633cd7b8
-/
theorem StartsAt.relabel {V : Type} {G : SimpleGraph V} {D : PathDecomposition G}
    {X : Finset V} (hstart : D.StartsAt X) (e : G ≃g H) :
    (D.relabel e).StartsAt (X.map e.toEquiv.toEmbedding) := by
  obtain ⟨first, hfirst, hX⟩ := hstart
  exact ⟨first, hfirst, congrArg (Finset.map e.toEquiv.toEmbedding) hX⟩

/-- A graph isomorphism preserves every bag's cardinality.
@isnad1 id=eq.0h7v.s5.f5179cce39f5 from=translated src=- shape=3956f9f4 vocab=634c1139
-/
theorem card_relabel_bag {V : Type} {G : SimpleGraph V} (D : PathDecomposition G)
    (e : G ≃g H) (i : Fin D.length) : ((D.relabel e).bag i).card = (D.bag i).card :=
  Finset.card_map _

/-- Appending a subset of the terminal bag preserves the bag-size bound.
@isnad1 id=ex.3h6v.s6.79fe5dba9b33 from=translated src=- shape=5fa10983 vocab=1d999f2c
-/
theorem EndsAt.exists_subset {D : PathDecomposition H} {X Y : Finset W}
    (hend : D.EndsAt Y) (hXY : X ⊆ Y) {b : Nat}
    (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt X ∧ ∀ i, (D'.bag i).card ≤ b :=
  Internal.exists_endsAt_subset D hend hXY bound

/-- Restore a deleted vertex in a new last bag. The last bag before
restoration must contain every neighbor; no other bag grows.
@isnad1 id=ex.4h6v.s8.f6d9f12f8087 from=translated src=- shape=3de579cf vocab=6d58f668
-/
theorem exists_restoreVertex (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v}))
    {Y : Finset {w : W // w ≠ v}} (hend : D.EndsAt Y)
    (neighbors : ∀ w, H.Adj v w → w ∈ Y.map (.subtype (· ≠ v)))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) (hY : Y.card + 1 ≤ b) :
    ∃ D' : PathDecomposition H,
      D'.EndsAt (insert v (Y.map (.subtype (· ≠ v)))) ∧
        ∀ i, (D'.bag i).card ≤ b :=
  Internal.exists_restoreVertex v D hend neighbors bound hY

/-- Delete a boundary vertex, then restore it and shrink the endpoint bag.
For the zero-neighbor case use `Y = X`; for a unique outside neighbor `u`,
use `Y = insert u X`. Only the new bag `Y` must fit the size bound.
@isnad1 id=ex.6h7v.s7.f551f9a189e3 from=translated src=- shape=02dacb94 vocab=cbfca63c
-/
theorem exists_endsAt_of_delete (v : W) {X Y : Finset W} (hv : v ∈ Y)
    (D : PathDecomposition (H.induce {w | w ≠ v}))
    (hend : D.EndsAt (Y.subtype (· ≠ v)))
    (neighbors : ∀ w, H.Adj v w → w ∈ Y) (hXY : X ⊆ Y)
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) (hY : Y.card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt X ∧ ∀ i, (D'.bag i).card ≤ b :=
  Internal.exists_endsAt_of_delete v hv D hend neighbors hXY bound hY

/-- Insert a deleted vertex into every bag, then append its singleton.
This costs at most one vertex per bag and needs no condition on its neighbors.
@isnad1 id=ex.1h5v.s7.85987a39bc00 from=translated src=- shape=8290732e vocab=b7a18761
-/
theorem exists_addVertex (v : W) (D : PathDecomposition (H.induce {w | w ≠ v}))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt {v} ∧ ∀ i, (D'.bag i).card ≤ b + 1 :=
  Internal.exists_addVertex v D bound

end Algebraic.Cutwidth.PathDecomposition
