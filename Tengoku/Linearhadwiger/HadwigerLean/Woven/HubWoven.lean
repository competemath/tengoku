import Tengoku.Linearhadwiger.HadwigerLean.Woven.HubInducedRouting

import Tengoku.Linearhadwiger.HadwigerLean.Woven.HubResidualControl

import Tengoku.Linearhadwiger.HadwigerLean.Woven.WovenSolutionFromPaths

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proxy woven solution from a clean mixed fan and linked hub

The paired incoming paths and hub linkage produce `m` disjoint paths.
Some carry proxy roots into a residual rooted model; the rest realize
terminal pairs while avoiding that model.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {a j m : ℕ}

end Woven
end HadwigerLean
