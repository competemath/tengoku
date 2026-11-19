import Tengoku.Linearhadwiger.HadwigerLean.Woven.NormalizedConstruction
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.ConnectivityDensity
import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.Theorem
import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueMinorOrder
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Wovenness through a rooted clique minor on normalized proxies

This checked route uses a complete minor on every proxy slot. It is useful
when the terminal budget is small enough for the clique-density threshold.
The sparse-target argument of Appendix F is needed for the sharper bound
linear in an arbitrarily large terminal budget.
-/

namespace HadwigerLean.Woven

universe u

end HadwigerLean.Woven
