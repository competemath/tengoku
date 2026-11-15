import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve

noncomputable def eichlerMass (N q : ℕ) : ℚ :=
  ((q : ℚ) - 1) * (dedekindPsi N : ℚ) / 12

noncomputable def ssCountFormula (N q : ℕ) : ℚ :=
  eichlerMass N q
    + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3

end ModularCurve
