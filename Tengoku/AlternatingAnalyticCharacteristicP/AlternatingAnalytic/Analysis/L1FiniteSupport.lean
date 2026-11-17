import Tengoku.Seed.Analysis.Normed.Lp.lpSpace
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-support approximation in ℓ¹

Coordinate expansions of continuous multilinear maps on ℓ¹(J, K) (the sum-norm `lp`
space) at finitely supported inputs, and convergence of these expansions under finite
truncation. The scalar field need not be complete.
-/

open scoped BigOperators lp
open Filter Topology

noncomputable section

namespace L1Coordinates

variable {K J W : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup W] [NormedSpace K W] {d : ℕ}

local instance : DecidableEq J := Classical.decEq J

end L1Coordinates
