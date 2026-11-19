import Tengoku.Linearhadwiger.HadwigerLean.Graph.Minor
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A clique embeds as a complete graph, hence gives a complete minor. -/

namespace HadwigerLean

/-- The largest clique order is bounded by the largest complete-minor order.
@isnad1 id=le.0h2v.s4.40b9abfba488 from=translated src=- shape=0afa9c3e vocab=47d90ad3
-/
theorem cliqueNum_le_cliqueMinorNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : G.cliqueNum ≤ cliqueMinorNumber G := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  let e := G.topEmbeddingOfNotCliqueFree hs.not_cliqueFree
  have h := cliqueMinorNumber_map e.toHom e.injective
  rw [cliqueMinorNumber_completeGraph] at h
  exact h

end HadwigerLean
