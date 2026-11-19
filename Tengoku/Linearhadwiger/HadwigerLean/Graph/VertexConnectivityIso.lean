import Tengoku.Linearhadwiger.HadwigerLean.Graph.VertexConnectivity
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vertex connectivity is invariant under finite graph isomorphisms
-/

namespace HadwigerLean

/-- Graph isomorphisms preserve vertex degree.
@isnad1 id=eq.0h6v.s7.37d3e43f6378 from=translated src=- shape=064e08a0 vocab=d2135d8e
-/
theorem degree_eq_of_iso
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (v : V) : G.degree v = H.degree (e v) := by
  classical
  let φ : G.neighborSet v ≃ H.neighborSet (e v) := {
    toFun := fun x => ⟨e x.1, e.map_rel_iff.mpr x.2⟩
    invFun := fun y => ⟨e.symm y.1, by
      have h := e.symm.map_rel_iff.mpr y.2
      simpa using h⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simp
    right_inv := by
      intro y
      apply Subtype.ext
      simp
  }
  calc
    G.degree v = Fintype.card (G.neighborSet v) := (G.card_neighborSet_eq_degree v).symm
    _ = Fintype.card (H.neighborSet (e v)) := Fintype.card_congr φ
    _ = H.degree (e v) := H.card_neighborSet_eq_degree (e v)

end HadwigerLean
