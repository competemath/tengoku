import Tengoku.Linearhadwiger.HadwigerLean.Graph.EdgeIncidenceMono
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Edge deletion preserves the massed shore bound at an edge-tight pair

If an edge has at least as many common neighbors as there are roots,
removing that edge cannot create a new separation whose adhesion is
smaller than the root set. Its possible crossing edge would force every
common neighbor into the adhesion.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges of a graph incident to a vertex set, viewed in the common
ambient symmetric-pair type.-/
private def incidentSym2 (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ w ∈ S, w ∈ e}

private theorem edgeIncidenceSetCount_eq_incident_ncard
    (G : SimpleGraph V) (S : Set V) :
    edgeIncidenceSetCount G S = (incidentSym2 G S).ncard := by
  let e : edgeIncidenceSet G S ≃ incidentSym2 G S := {
    toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  exact Nat.card_congr e

/-- Deleting an existing edge meeting the outside of `X` removes exactly
one edge from the outside-incidence count.-/
theorem edgeIncidenceSetCount_delete_edge_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (huv : G.Adj u v)
    (hout : u ∉ X ∨ v ∉ X) :
    edgeIncidenceSetCount (G.deleteEdges {s(u, v)}) (X : Set V)ᶜ + 1 =
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
  classical
  let e : Sym2 V := s(u, v)
  let S : Set V := (X : Set V)ᶜ
  have hmem : e ∈ incidentSym2 G S := by
    refine ⟨by simpa [e] using huv, ?_⟩
    rcases hout with hu | hv
    · exact ⟨u, by simpa [S] using hu, by simp [e]⟩
    · exact ⟨v, by simpa [S] using hv, by simp [e]⟩
  have hset : incidentSym2 (G.deleteEdges {s(u, v)}) S =
      incidentSym2 G S \ {e} := by
    ext f
    simp [incidentSym2, SimpleGraph.edgeSet_deleteEdges, e]
    tauto
  rw [edgeIncidenceSetCount_eq_incident_ncard,
    edgeIncidenceSetCount_eq_incident_ncard, hset]
  exact Set.ncard_sdiff_singleton_add_one hmem (by toFinite_tac)
/-- The exact global incidence count (D.3) at an edge-tight massed pair.
Minimality supplies failure of the strict global inequality after one
exterior edge is deleted; the original pair has the strict inequality.-/
theorem massed_global_edge_tight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (r : ℕ)
    (hm : MassedPair G (X : Set V) (r : ℝ))
    (u v : V) (huv : G.Adj u v)
    (hout : u ∉ X ∨ v ∉ X)
    (hfail : ¬ ((r : ℝ) * (Nat.card {w : V // w ∉ (X : Set V)} : ℝ) <
      (edgeIncidenceSetCount (G.deleteEdges {s(u, v)}) (X : Set V)ᶜ : ℝ))) :
    edgeIncidenceSetCount G (X : Set V)ᶜ =
      r * ((X : Set V)ᶜ).ncard + 1 := by
  have hdrop := edgeIncidenceSetCount_delete_edge_add_one G X u v huv hout
  have hN : Nat.card {w : V // w ∉ (X : Set V)} =
      ((X : Set V)ᶜ).ncard := rfl
  have hglobal : r * ((X : Set V)ᶜ).ncard <
      edgeIncidenceSetCount G (X : Set V)ᶜ := by
    change r * Nat.card {w : V // w ∉ (X : Set V)} <
      edgeIncidenceSetCount G (X : Set V)ᶜ
    exact_mod_cast hm.global
  have hfailNat : edgeIncidenceSetCount
      (G.deleteEdges {s(u, v)}) (X : Set V)ᶜ ≤
      r * ((X : Set V)ᶜ).ncard := by
    have hf := le_of_not_gt hfail
    change edgeIncidenceSetCount (G.deleteEdges {s(u, v)})
      (X : Set V)ᶜ ≤ r * Nat.card {w : V // w ∉ (X : Set V)}
    exact_mod_cast hf
  omega

end Linkedness
end HadwigerLean
