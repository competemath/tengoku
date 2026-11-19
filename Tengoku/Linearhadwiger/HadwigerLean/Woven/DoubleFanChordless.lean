import Tengoku.Linearhadwiger.HadwigerLean.Woven.DoubleFan
import Tengoku.Linearhadwiger.HadwigerLean.ReedSeymour.ConnectorLift
import Tengoku.Linearhadwiger.HadwigerLean.ReedSeymour.Parity
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shortening each double-fan path inside its own support
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V}

end Woven
end HadwigerLean
