import Tengoku.NavierStokesEuler.Euler.ParameterWordProduct
import Tengoku.NavierStokesEuler.Euler.BoundedInverseGevrey

/-!
# A genuine inverse recurrence for the unchanged word sums

Freeze the actual left inverse at a parameter value. The coefficient
difference vanishes there, so the direct word-product estimate removes the
top unknown term. The same factorial radius is used for input and output.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

end EulerParameterWordGevrey
