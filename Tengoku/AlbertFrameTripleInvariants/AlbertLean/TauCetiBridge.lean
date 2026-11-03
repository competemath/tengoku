import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ModelIdentification
import Tengoku
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bridge to Tau Ceti's split Albert algebra

This file gives the literal coordinate dictionary between the local Zorn and
Hermitian models and the conventional models in Tau Ceti.  The order of the
three off-diagonal entries is `(23,31,12)`, and the two three-vectors in a Zorn
matrix retain their order and signs.
-/

noncomputable section

namespace AlbertLean

local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
attribute [local simp] Matrix.vec3_dotProduct cross_apply
  Matrix.vecHead Matrix.vecTail

end AlbertLean
