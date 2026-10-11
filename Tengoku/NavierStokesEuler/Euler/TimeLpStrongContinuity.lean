import Tengoku.NavierStokesEuler.Euler.TimeLpBoundedMap
import Tengoku

/-!
# Strong continuity of isometric spatial actions on time L²

This uses dominated convergence with the actual square-integrable time field.
It does not assume operator-norm continuity of spatial translations.
-/

noncomputable section

namespace EulerTimeLpBoundedMap

open MeasureTheory Set Filter EulerTimeLp
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end EulerTimeLpBoundedMap
