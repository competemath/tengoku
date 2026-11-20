import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/- A dyadic cycle in an induced graph remains dyadic after inclusion in the
   ambient graph.  The embedding is injective, so simplicity is preserved. -/
theorem hasPowerOfTwoCycle_of_induce
    {V : Type u} {G : SimpleGraph V} {S : Set V}
    (hcycle : HasPowerOfTwoCycle (G.induce S)) :
    HasPowerOfTwoCycle G := by
  rcases hcycle with ⟨k, v, c, hk, hc, hlen⟩
  let e : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  refine ⟨k, e v, c.map e.toHom, hk, ?_, ?_⟩
  · exact hc.map e.injective
  · rw [SimpleGraph.Walk.length_map]
    exact hlen

/- Ambient absence of a dyadic cycle transfers to every induced subgraph. -/
theorem not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle
    {V : Type u} {G : SimpleGraph V} {S : Set V}
    (hno : ¬ HasPowerOfTwoCycle G) :
    ¬ HasPowerOfTwoCycle (G.induce S) := by
  intro hcycle
  exact hno (hasPowerOfTwoCycle_of_induce hcycle)

/- Root-deleted spelling for downstream strict-descent code.  The root
   exclusion is retained in the interface, although transfer itself is
   independent of it. -/
theorem not_hasPowerOfTwoCycle_rootDeleted_induce
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hno : ¬ HasPowerOfTwoCycle G) (r : V) (S : Finset V)
    (hrS : r ∉ S) :
    ¬ HasPowerOfTwoCycle (G.induce (↑S : Set V)) := by
  exact not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle hno

end Erdos64
