import Tengoku.Erdos64.Erdos64.StrictRootedDoubleClosedSide
import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Identifying the two roots does not identify edges: every original edge
has exactly two copies in the rooted double.-/
theorem rootedDouble_edge_count
    {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (r : V) :
    (rootedDoubleGraph G r).edgeFinset.card = 2 * G.edgeFinset.card := by
  classical
  have hsum : (∑ z, (rootedDoubleGraph G r).degree z) =
      2 * ∑ v, G.degree v := by
    rw [Fintype.sum_option]
    simp_rw [Fintype.sum_prod_type, rootedDouble_nonroot_degree_preservation]
    rw [Fintype.sum_bool, rootedDouble_root_degree_doubling,
      Fintype.sum_eq_add_sum_subtype_ne (fun v => G.degree v) r]
    omega
  rw [(rootedDoubleGraph G r).sum_degrees_eq_twice_card_edges,
    G.sum_degrees_eq_twice_card_edges] at hsum
  omega

/-- The edge-set cardinality formulation of `rootedDouble_edge_count`.-/
theorem rootedDouble_edgeSet_ncard
    {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (r : V) :
    (rootedDoubleGraph G r).edgeSet.ncard = 2 * G.edgeSet.ncard := by
  classical
  simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
    using rootedDouble_edge_count G r

/-- A closed side with at least two root neighbors doubles to a counterexample.
No strict order bound is needed for counterexample preservation; a size bound
is required only when this construction is used for a descent argument.-/
theorem rootedDouble_closed_side_isCounterexample
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hce : IsCounterexample G)
    (S : Finset V) (r : {v : V // v ∈ S})
    (hclosed : ∀ v, v ∈ S → v ≠ r.val →
      ∀ w, G.Adj v w → w ∈ S)
    (hroot : 2 ≤ internalDegree G S r.val) :
    IsCounterexample (rootedDoubleGraph (G.induce (↑S : Set V)) r) := by
  classical
  constructor
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

end Erdos64
