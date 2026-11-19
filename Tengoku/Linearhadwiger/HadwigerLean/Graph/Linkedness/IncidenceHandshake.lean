import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

private def exteriorGraph (G : SimpleGraph V) (X : Finset V) : SimpleGraph V :=
  G.deleteEdges (X.sym2 : Set (Sym2 V))

end Linkedness
end HadwigerLean

namespace HadwigerLean
namespace Linkedness

end Linkedness
end HadwigerLean

namespace HadwigerLean
namespace Linkedness

end Linkedness
end HadwigerLean

namespace HadwigerLean
namespace Linkedness

end Linkedness
end HadwigerLean
