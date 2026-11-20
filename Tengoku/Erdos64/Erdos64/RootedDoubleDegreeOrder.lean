import Tengoku.Erdos64.Erdos64.RootedDoubleNonroot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Degree and order facts for doubling a closed finite side.  The theorem
does not assemble a counterexample: it only transports the supplied ambient
side degree bounds and root internal degree to the rooted double.
@isnad1 id=and.4h4v.s10.9ceb44fc599f from=translated src=- shape=3f96f3e3 vocab=dd29763f
-/
theorem rootedDouble_degree_order_interface
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) (r : {v : V // v ∈ S})
    (hclosed : ∀ v, v ∈ S → v ≠ r.val →
      ∀ w, G.Adj v w → w ∈ S)
    (hroot : 2 ≤ internalDegree G S r.val)
    (hside : ∀ v, v ∈ S → 3 ≤ G.degree v)
    (hsize : 2 * S.card - 1 < Fintype.card V) :
    (∀ (b : Bool) (v : {v : (↑S : Set V) // v ≠ r}),
      3 ≤ (rootedDoubleGraph (G.induce (↑S : Set V)) r).degree
        (some (b, v))) ∧
    4 ≤ (rootedDoubleGraph (G.induce (↑S : Set V)) r).degree none ∧
    Fintype.card (RootedDoubleVertex (↑S : Set V) r) = 2 * S.card - 1 ∧
    Fintype.card (RootedDoubleVertex (↑S : Set V) r) < Fintype.card V := by
  classical
  have hnonroot :
      ∀ (b : Bool) (v : {v : (↑S : Set V) // v ≠ r}),
        3 ≤ (rootedDoubleGraph (G.induce (↑S : Set V)) r).degree
          (some (b, v)) := by
    intro b v
    rw [rootedDouble_nonroot_degree_preservation]
    rw [degree_induce_coeFinset_eq_internalDegree (G := G) v.1]
    have hvroot : v.1.1 ≠ r.val := by
      intro heq
      apply v.2
      exact Subtype.ext heq
    have hneighbors : S.filter (G.Adj v.1.1) = G.neighborFinset v.1.1 := by
      ext w
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · exact And.right
      · intro hadj
        exact ⟨hclosed v.1.1 v.1.property hvroot w hadj, hadj⟩
    change 3 ≤ (S.filter (G.Adj v.1.1)).card
    rw [hneighbors, SimpleGraph.card_neighborFinset_eq_degree]
    exact hside v.1.1 v.1.property
  have hrootDouble :
      4 ≤ (rootedDoubleGraph (G.induce (↑S : Set V)) r).degree none := by
    rw [rootedDouble_root_degree_doubling,
      degree_induce_coeFinset_eq_internalDegree (G := G) r]
    omega
  have hcard :
      Fintype.card (RootedDoubleVertex (↑S : Set V) r) = 2 * S.card - 1 := by
    rw [rootedDouble_card]
    have hsidecard : Fintype.card (↑S : Set V) = S.card :=
      Fintype.card_of_finset' S (fun _ => Iff.rfl)
    rw [hsidecard]
  refine ⟨hnonroot, hrootDouble, hcard, ?_⟩
  rw [hcard]
  exact hsize

end Erdos64
