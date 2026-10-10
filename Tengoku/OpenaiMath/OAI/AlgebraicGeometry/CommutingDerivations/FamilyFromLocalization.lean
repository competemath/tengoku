import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.DenominatorDescent
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.DescentFamily
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.LocalizedPartials

namespace OAI

/-!
Construction of a commuting, locally nilpotent, linearly independent family
from a relative localization equivalence and a coefficient-intersection identity.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L σ τ : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L] [Algebra (MvPolynomial σ K) L]
  [IsScalarTower K (MvPolynomial σ K) L] [Fintype σ] [Fintype τ]
  [IsDomain B] [CharZero B]

end AbhyankarSathaye.CommutingDerivations

end

end OAI
