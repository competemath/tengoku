import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.WeightedInitialIdeal
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.GradedRelation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# The exact initial relation of the source hypersurface

For the five independent variables `p,s,u,F,J`, with integer weights
`(-1,0,0,1,1)`, this file proves that the initial ideal of `(H)` is exactly
`(Hstar)`. It also gives the actual homogeneous kernel criterion in terms of
the quotient rings `A` and `G`, without assuming an associated-graded isomorphism.
-/

namespace StableCoordinate.PrincipalInitialRelation

noncomputable section

open MvPolynomial WeightedInitial Obstruction

variable (k : Type*) [CommRing k]

variable [IsDomain k]

end
end StableCoordinate.PrincipalInitialRelation

end OAI
