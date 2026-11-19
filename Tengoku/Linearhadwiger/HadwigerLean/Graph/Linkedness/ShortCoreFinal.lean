import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.ShortCoreResidual
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.ShortCoreResidualDegree
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.InducedTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The short-path small-core argument
-/

namespace HadwigerLean
namespace Linkedness

set_option maxHeartbeats 1000000

/-- A disconnected graph meeting the 14k/5k bounds contains a
k-linked induced subgraph of order at most 7k.
@isnad1 id=ex.3h5v.s7.d44b660af2cb from=translated src=- shape=8f24a971 vocab=a0ddc5ff
-/
theorem linked_side_of_nonreachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (horder : Fintype.card V ≤ 14 * k)
    (hdegree : ∀ x, 5 * k ≤ H.degree x)
    (u v : V) (huv : ¬ H.Reachable u v) :
    ∃ S : Finset V, S.Nonempty ∧ S.card ≤ 7 * k ∧
      KLinked (H.induce (S : Set V)) k := by
  classical
  let A : Finset V := Finset.univ.filter (fun x => H.Reachable u x)
  let B : Finset V := Aᶜ
  have hcover : A ∪ B = Finset.univ := Finset.union_compl A
  have hdisjoint : Disjoint A B := by
    change Disjoint A Aᶜ
    exact disjoint_compl_right
  have hnoedge : ∀ x ∈ A, ∀ y ∈ B, ¬ H.Adj x y := by
    intro x hx y hy hxy
    have hux : H.Reachable u x := (Finset.mem_filter.mp hx).2
    have huy : H.Reachable u y := hux.trans hxy.reachable
    have hyA : y ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huy⟩
    exact (Finset.mem_compl.mp hy) hyA
  have hA : A.Nonempty := by
    refine ⟨u, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl u⟩
  have hB : B.Nonempty := by
    refine ⟨v, ?_⟩
    apply Finset.mem_compl.mpr
    intro hvA
    exact huv (Finset.mem_filter.mp hvA).2
  exact linked_side_of_dense_anticomplete_partition H k
    horder hdegree A B hcover hdisjoint hA hB hnoedge

namespace ShortPartial

/-- A vertex whose degree exceeds the occupied set has an exterior
neighbor.
@isnad1 id=ex.1h6v.s7.c5adac894b2a from=translated src=- shape=1fe68cba vocab=8814f618
-/
theorem exterior_neighbor_of_degree_gt_occupied
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {P : IndexedPairs (Fin k) V}
    (C : ShortPartial G P (terminalFinset P))
    (s : V) (hdegree : C.occupied.card < G.degree s) :
    ∃ u : {x : V | x ∉ C.occupied}, G.Adj s u.1 := by
  classical
  by_contra h
  have hsub : G.neighborFinset s ⊆ C.occupied := by
    intro u hu
    by_contra hnot
    have hadj : G.Adj s u := (G.mem_neighborFinset s u).mp hu
    exact h ⟨⟨u,hnot⟩,hadj⟩
  have hcard := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at hcard
  omega

/-- A partial linkage with no full extension leaves one index unused.
@isnad1 id=ex.1h6v.s6.c649c59728bf from=translated src=- shape=bab359eb vocab=a9b67d11
-/
theorem exists_unused_index
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    {P : IndexedPairs (Fin k) V} {X : Finset V}
    (C : ShortPartial G P X)
    (hnot : ¬ Nonempty (IndexedLinkage G P)) :
    ∃ i : Fin k, i ∉ C.used := by
  classical
  by_contra h
  have hfull : C.used = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i,hi⟩
  have hcardfull : C.used.card = k := by
    rw [hfull]
    simp
  exact hnot ⟨C.toLinkageOfFull hcardfull⟩

end ShortPartial

end Linkedness
end HadwigerLean
