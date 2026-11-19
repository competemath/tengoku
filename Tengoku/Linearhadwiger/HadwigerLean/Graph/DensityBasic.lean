import Tengoku.Linearhadwiger.HadwigerLean.Graph.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite edge counts and density

The density used in the proof is the number of edges divided by the number
of vertices.  Edge incidence counts record edges with at least one endpoint
in a selected vertex set, as in the massed-pair argument.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V]

/-- Number of edges of a finite simple graph.-/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/-- Number of edges touching at least one vertex of `S`.-/
noncomputable def edgeIncidenceCount (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (G.edgeFinset.filter fun e => ∃ v ∈ S, v ∈ e).card

/-- The edge-per-vertex density, with zero density for the empty graph.-/
noncomputable def edgeDensity (G : SimpleGraph V) : ℝ :=
  (edgeCount G : ℝ) / (Fintype.card V : ℝ)

/--
@isnad1 id=eq.0h2v.s5.57deefebf25a from=translated src=- shape=386168a7 vocab=7d74c920
-/
theorem edgeCount_eq_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  simpa [edgeCount, Nat.card_eq_fintype_card] using G.edgeFinset_card.symm

/--
@isnad1 id=eq.0h2v.s4.9289ed99cbb9 from=translated src=- shape=fa71c1ef vocab=c658afd4
-/
theorem edgeIncidenceCount_empty (G : SimpleGraph V) :
    edgeIncidenceCount G ∅ = 0 := by
  classical
  simp [edgeIncidenceCount]

/--
@isnad1 id=le.1h4v.s5.14c7cebd4ffc from=translated src=- shape=d7de5d8b vocab=85490398
-/
theorem edgeIncidenceCount_mono (G : SimpleGraph V)
    {S T : Finset V} (hST : S ⊆ T) :
    edgeIncidenceCount G S ≤ edgeIncidenceCount G T := by
  classical
  unfold edgeIncidenceCount
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  obtain ⟨hEdge, v, hv, hve⟩ := he
  exact ⟨hEdge, v, hST hv, hve⟩

/--
@isnad1 id=le.0h3v.s4.6a6b99a0838d from=translated src=- shape=5ec62e96 vocab=5caa0ae3
-/
theorem edgeIncidenceCount_le_edgeCount (G : SimpleGraph V) (S : Finset V) :
    edgeIncidenceCount G S ≤ edgeCount G := by
  classical
  unfold edgeIncidenceCount
  rw [edgeCount_eq_card_edgeFinset]
  exact Finset.card_filter_le _ _

/-- The handshaking identity in the local edge-count notation.
@isnad1 id=eq.0h2v.s6.75e14f7eee96 from=translated src=- shape=456009b4 vocab=37af8156
-/
theorem sum_degree_eq_two_edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, G.degree v) = 2 * edgeCount G := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  exact G.sum_degrees_eq_twice_card_edges

/--
@isnad1 id=le.0h2v.s4.7d3f5435b496 from=translated src=- shape=38fc717e vocab=7d9cd444
-/
theorem edgeDensity_nonneg (G : SimpleGraph V) : 0 ≤ edgeDensity G := by
  unfold edgeDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end HadwigerLean
