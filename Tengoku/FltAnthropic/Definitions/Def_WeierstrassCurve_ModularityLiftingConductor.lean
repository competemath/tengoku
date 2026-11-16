import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_ModularRep
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_Mlc1RowStatement
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_ModularityProps
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_Semistability
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_ThreeFiveSwitchConditioned

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

abbrev IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  Mlc1IsModularModelOfExactConductorLevel W

namespace IsModularModelOfExactConductorLevel

end IsModularModelOfExactConductorLevel

abbrev ModularityLiftingAtConductor (p : ℕ) : Prop :=
  Mlc1ModularityLiftingAtConductor p

def ModularityLiftingAtConductorOrdinary (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
    W.IsResiduallyModular p → W.IsModularModelOfExactConductorLevel

end WeierstrassCurve

namespace FreyPackage

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

noncomputable local instance instDecEqQbarLedgerStageTwo :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end
