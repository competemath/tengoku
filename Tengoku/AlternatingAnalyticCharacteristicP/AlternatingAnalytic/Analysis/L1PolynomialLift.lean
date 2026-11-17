import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1Coordinates
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.FiniteWordGrouping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting homogeneous diagonals on ℓ¹

If a bounded `d`-linear map `B` on ℓ¹(J, K) has its diagonal in a closed subspace `W` of a
Banach space, there is a `W`-valued `d`-linear map with the same diagonal and norm at most
`d! * ‖B‖`. This is the sorting bound in the proof of Theorem 4.5(2). The coefficients are
the sums of `B` over permutations of sorted words (`FiniteWord.groupedCoefficient`); the
factorial counts terms and is never inverted, so any characteristic is allowed.
-/

open scoped lp BigOperators
open Filter Topology

namespace L1PolynomialLift

variable {K J Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z]

noncomputable local instance : DecidableEq J := Classical.decEq J

variable {d : ℕ}

end L1PolynomialLift
