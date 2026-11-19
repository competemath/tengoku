import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.ShortCoreStrong
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.InducedTransport
import Tengoku.Linearhadwiger.HadwigerLean.Graph.VertexConnectivityIso
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transfer of a dense linked core from a residual graph
-/

namespace HadwigerLean
namespace Linkedness

/-- A core of order at most `7k` and minimum degree at least `5k`
links every pairing of at most `2k` prescribed roots while avoiding all
other roots.-/
theorem rootedLinked_of_five_mul_degree_seven_mul_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdegree : ∀ v, 5 * k ≤ G.degree v)
    (horder : Fintype.card V ≤ 7 * k)
    (Y : Finset V) (hY : Y.card ≤ 2 * k) :
    RootedLinked G Y := by
  classical
  intro n P hP hne hPY
  have hsubset : terminalFinset P ⊆ Y := by
    intro v hv
    rcases (mem_terminalFinset P v).mp hv with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hPY i (by simp [IndexedPairs.terminals, hi])
    · exact hPY i (by simp [IndexedPairs.terminals, hi])
  have hcard := terminalFinset_card_eq_two_mul n P hP hne
  have hcardY := Finset.card_le_card hsubset
  have hn : n ≤ k := by omega
  have hsize : Fintype.card V + 3 * k ≤ 2 * (5 * k) := by omega
  apply rooted_linkage_of_common_neighbors G Y n P hP hne hPY
  intro i
  exact hn.trans (commonOutside_card_ge_of_minDegree G k (5 * k)
    hdegree hsize Y hY (P.start i) (P.finish i))

end Linkedness
end HadwigerLean
