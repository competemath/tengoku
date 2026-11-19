import Tengoku.Linearhadwiger.HadwigerLean.Woven.HubPathSplice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residual-set control for paths spliced through a hub
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {P : IndexedPairs ι V}
  {H U : Finset V} {m : ℕ}

end Woven
end HadwigerLean
