import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative linkedness: checked reductions

Appendix D reduces `16k`-connectivity to massed-pair rooted linkedness.
The complete result is in `Linkedness/Final.lean`.
-/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The strengthened numerical criterion holds for the `5k`-minimum-degree,
`7k`-vertex component extracted in Appendix D.
@isnad1 id=klinked.2h3v.s6.82233620c37c from=translated src=- shape=68c105ed vocab=f1f24b73
-/
theorem kLinked_of_five_k_degree_seven_k_order (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hdegree : ∀ v, 5 * k ≤ G.degree v)
    (horder : Fintype.card V ≤ 7 * k) :
    KLinked G k := by
  apply kLinked_of_high_minDegree G k (5 * k) hdegree
  omega

/-- A `16k`-connected graph of order at most `29k` is linked directly by
the common-neighbor criterion.
@isnad1 id=klinked.2h3v.s5.2d1a73b0a2fd from=translated src=- shape=2fd6551b vocab=696c6112
-/
theorem kLinked_of_connected_small_order (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hconn : VertexConnected G (16 * k))
    (horder : Fintype.card V ≤ 29 * k) :
    KLinked G k := by
  apply kLinked_of_high_minDegree G k (16 * k)
  · intro v
    exact degree_ge_of_vertexConnected hconn v
  · omega

end Linkedness
end HadwigerLean
