import Tengoku.GeneralStochToDet.stoch_to_det.Main
import Tengoku.GeneralStochToDet.stoch_to_det.SeedConstant1771

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The improved finite-latent stoch_to_det theorem

This module proves the improved finite theorem. It reuses the
audited seed, cell, and connected-component reductions, changing only the
quantitative inputs proved in the improved modules.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

end stoch_to_det
