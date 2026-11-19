import Tengoku.Linearhadwiger.HadwigerLean.Woven.NormalizedConstruction
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.Dichotomy
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The normalized clique-minor base of the woven induction

The minor and connectivity tests are on the graph after deleting all
original role vertices. Distinct adjacent proxies serve as roots there.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {a j : ℕ}

/-- The ambient connectivity budget guarantees connectivity of the graph
after deleting the occupied roles.
@isnad1 id=ex.2h7v.s7.e9d25151fe2b from=translated src=- shape=14a8d731 vocab=3383361f
-/
theorem normalized_connected_of_budget
    {G : SimpleGraph V}
    (root : Fin a → V) (P : IndexedPairs (Fin j) V)
    {K : ℕ} (hconn : VertexConnected G K)
    (hbudget : 2 * (a + 2 * j) ≤ K) :
    ∃ inst : Fintype (normalizedSet root P),
      @VertexConnected (normalizedSet root P) inst
        (G.induce (normalizedSet root P)) (a + 2 * j) := by
  classical
  have hcard := occupiedRoles_card_le root P
  have hbudget' : (occupiedRoles root P).card + (a + 2 * j) ≤ K := by
    omega
  exact ⟨(inferInstance : Fintype (↥(((occupiedRoles root P : Finset V) : Set V)ᶜ))),
    hconn.induce_compl (occupiedRoles root P) (a + 2 * j) hbudget'⟩

end Woven
end HadwigerLean
