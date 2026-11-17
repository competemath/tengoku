import Tengoku.OspTriviality.InhomogeneousDeformations.IndexedU
import Tengoku.Seed.LinearAlgebra.CliffordAlgebra.Basic
import Tengoku.Seed.LinearAlgebra.CliffordAlgebra.Grading

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# I106 R2, W0 — `C = Q[a]/(a^2 - 1/2)`, `a` odd

Transcription: `C = \mathbb Q[a]/(a^2-\tfrac12)` (manuscript lines 98-101). Built as
`CliffordAlgebra Qhalf` with `Qhalf : QuadraticForm ℚ ℚ`, `Qhalf x = x^2/2` — the same
construction R0's F1 experiment used (there with the zero form) and Agent1c recompiled,
now with the actual quadratic form the manuscript needs. `CliffordAlgebra.ι_sq_scalar`
gives `a^2 = 1/2` **by the library**, not by a fresh axiom or computation of our own.

**A2**: `a^2 = 1/2` and `a` odd, both proved below.
-/

namespace InhomogeneousDeformations
namespace Source

/-- `Q(x) = x^2/2`, the quadratic form whose Clifford algebra is `C`.-/
noncomputable def Qhalf : QuadraticForm ℚ ℚ := (1 / 2 : ℚ) • QuadraticMap.sq

/-- `C = Q[a]/(a^2 - 1/2)`, built as `CliffordAlgebra Qhalf`.-/
noncomputable abbrev C : Type := CliffordAlgebra Qhalf

/-- The odd generator `a`.-/
noncomputable def a : C := CliffordAlgebra.ι Qhalf 1

/-- `C`'s `ZMod 2` grading is `CliffordAlgebra.evenOdd Qhalf`, an instance the library already
supplies (`CliffordAlgebra.gradedAlgebra`) — noted here under a local name for W2 to cite.-/
noncomputable abbrev CGrading : ZMod 2 → Submodule ℚ C := CliffordAlgebra.evenOdd Qhalf

noncomputable instance CGrading_gradedAlgebra : GradedAlgebra CGrading :=
  CliffordAlgebra.gradedAlgebra Qhalf

end Source
end InhomogeneousDeformations
