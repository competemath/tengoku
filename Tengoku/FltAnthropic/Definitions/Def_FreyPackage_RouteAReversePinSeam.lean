import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_ModularRep
import Tengoku.FltAnthropic.Definitions.Def_FreyPackage_LevelRaising
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

set_option maxHeartbeats 600000

open WeierstrassCurve WeierstrassCurve.Affine.Point CuspForm

open scoped CongruenceSubgroup

namespace Tengoku.FltAnthropic.FreyPackage

def FreyCurveApOfModelThreeAgreement (P : FreyPackage) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.IsIntegralModelOf P.freyCurve →
    W.IsGoodPrimeFor 3 → W.apOfModel 3 = 0

def RouteAReversePinBadOnlySeam (P : FreyPackage) : Prop :=
  ∀ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)), P.IsCongruentWitness N f W 𝔪 →
    ∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ¬ W.IsGoodPrimeFor ℓ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end Tengoku.FltAnthropic.FreyPackage
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
