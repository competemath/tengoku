import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.CliqueBridge
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Vertex connectivity supplies the density used by the clique bridge. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- The edge-per-vertex density is at least half the vertex-connectivity
parameter, by minimum degree and handshaking.-/
theorem half_connectivity_le_edgeDensity
    {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hconn : VertexConnected G k) :
    (k : ℝ) / 2 ≤ edgeDensity G := by
  classical
  have hdeg : ∀ v : V, k ≤ G.degree v := by
    intro v
    exact Linkedness.degree_ge_of_vertexConnected hconn v
  have hsum : k * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc
      k * Fintype.card V = ∑ _v : V, k := by simp [mul_comm]
      _ ≤ ∑ v : V, G.degree v := by
        apply Finset.sum_le_sum
        intro v _
        exact hdeg v
  rw [sum_degree_eq_two_edgeCount] at hsum
  have hsumR : (k : ℝ) * (Fintype.card V : ℝ) ≤
      2 * (edgeCount G : ℝ) := by exact_mod_cast hsum
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (Nat.zero_lt_of_lt hconn.order_gt)
  unfold edgeDensity
  apply (le_div_iff₀ hn).2
  nlinarith

end HadwigerLean.RootedDensity
