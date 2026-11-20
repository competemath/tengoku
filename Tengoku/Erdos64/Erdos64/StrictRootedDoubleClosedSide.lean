import Tengoku.Erdos64.Erdos64.RootedDoubleNonroot
import Tengoku.Erdos64.Erdos64.RootedDoubleProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

set_option maxHeartbeats 800000 in
/-- Doubling a closed side gives a strictly smaller counterexample when the
root retains at least two neighbors and the doubled order is strictly smaller.
The side and the strict size bound are supplied, not inferred.
@isnad1 id=isstrict.4h4v.s9.fd2f22e9e1da from=translated src=- shape=9d23fa9a vocab=a290e2bc
-/
theorem strict_double_of_closed_side
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hce : IsCounterexample G)
    (S : Finset V) (r : {v : V // v ∈ S})
    (hclosed : ∀ v, v ∈ S → v ≠ r.val →
      ∀ w, G.Adj v w → w ∈ S)
    (hroot : 2 ≤ internalDegree G S r.val)
    (hsize : 2 * S.card - 1 < Fintype.card V) :
    IsStrictlySmallerCounterexample G
      (rootedDoubleGraph (G.induce (↑S : Set V)) r) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro z
    cases z with
    | none =>
        rw [rootedDouble_root_degree_doubling,
          degree_induce_coeFinset_eq_internalDegree G r]
        omega
    | some bv =>
        rcases bv with ⟨b, v⟩
        rw [rootedDouble_nonroot_degree_preservation]
        have hvroot : v.val.val ≠ r.val := by
          intro heq
          exact v.property (Subtype.ext heq)
        have hneighbors : S.filter (G.Adj v.val.val) =
            G.neighborFinset v.val.val := by
          ext w
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨And.right, fun hadj =>
            ⟨hclosed v.val.val v.val.property hvroot w hadj, hadj⟩⟩
        rw [degree_induce_coeFinset_eq_internalDegree G v.val]
        change 3 ≤ (S.filter (G.Adj v.val.val)).card
        rw [hneighbors, SimpleGraph.card_neighborFinset_eq_degree]
        exact degree_ge_three_of_minDegree_ge_three G hce.1 v.val.val
  · intro hdouble
    rcases hdouble with ⟨k, z, c, hk, hc, hlength⟩
    have hproject_cycle := (rootedDouble_cycle_projection c hc).1
    let inclusion : G.induce (↑S : Set V) →g G :=
      { toFun := Subtype.val
        map_rel' := by
          intro a b hab
          exact hab }
    refine hce.2 ⟨k, _, (c.map rootedDoubleProjectionHom).map inclusion,
      hk, hproject_cycle.map Subtype.val_injective, ?_⟩
    simpa only [SimpleGraph.Walk.length_map] using hlength
  · rw [rootedDouble_card]
    have hcard : Fintype.card (↑S : Set V) = S.card :=
      Fintype.card_of_finset' S (fun _ => Iff.rfl)
    rw [hcard]
    exact hsize

end Erdos64
