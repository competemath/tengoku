import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.AbsorptionCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From a uniformly invertible diagonal bridge to the identity-corner theorem

A diagonal similarity turns the bridge into an identity. Both the similarity and
its inverse are explicit, and the final factors remain in the original space.
-/

open scoped Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {d : ι → Type} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- The first half of the core is scaled; all other coordinates are fixed.-/
def bridgeWeights (δ : Fin r → ℝ) : Ambient r d → ℂ
  | ⟨none, Sum.inl i⟩ => δ i
  | ⟨none, Sum.inr _⟩ => 1
  | ⟨some _, _⟩ => 1

end NoEpsilon.Absorption
