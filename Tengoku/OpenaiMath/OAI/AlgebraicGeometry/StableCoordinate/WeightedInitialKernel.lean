import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.WeightedInitial
import Tengoku.Seed.RingTheory.Ideal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# The homogeneous kernel criterion for a principal filtered quotient

A homogeneous polynomial disappears in the associated graded quotient by `(H)`
exactly when it is divisible by the highest component of `H`. The statement is
expressed in terms of representatives of lower weight; it thus supplies the
kernel computation independently of a particular associated-graded construction.
-/

namespace StableCoordinate
namespace WeightedInitial

open MvPolynomial

variable {σ K : Type*} [CommRing K] [IsDomain K]

omit [IsDomain K] in
lemma bounded_of_homogeneous {w : σ → ℤ} {p : MvPolynomial σ K} {d : ℤ}
    (hp : IsWeightedHomogeneous w p d) : Bounded w p d :=
  fun _ hm => (hp hm).le

end WeightedInitial
end StableCoordinate

end OAI
