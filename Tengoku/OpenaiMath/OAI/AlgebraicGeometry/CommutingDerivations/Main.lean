import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.CoefficientInstances
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.ExtendedLocalization
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.ExtendedKernelIntersection
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.FamilyFromLocalization
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.KernelObstruction

namespace OAI

/-!
Commuting locally nilpotent derivations for the explicit Abhyankar polynomial
in every dimension `n ≥ 4`, with common kernel `ℂ[Fₙ]`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem extendedF_four : extendedF (by decide : 4 ≤ 4) = F := by
  have hi : fourInclusion (by decide : 4 ≤ 4) = id := by
    funext i
    apply Fin.ext
    rfl
  unfold extendedF
  rw [hi, rename_id]
  rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI
