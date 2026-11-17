import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1WordSeries
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1WordSynthesis
import Tengoku.Seed.Analysis.Analytic.Basic
import Tengoku.Seed.Analysis.Normed.Module.Completion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local factorization of analytic maps on ℓ¹

An analytic map `γ` on `ℓ¹(I, K)` factors locally as `T ∘ g`, where
`g(x)_{n,a} = s⁻ⁿ x_{a_1} ⋯ x_{a_n}` is analytic into `ℓ¹` over finite words and
`T(e_{n,a}) = sⁿ aₙ(e_{a_1}, …, e_{a_n})` is bounded linear into the completion of the
output. This is the factorization step in the proof of Theorem 4.5(2). The field `K`
need not be complete.
-/

open scoped lp BigOperators ENNReal
open Filter Topology

noncomputable section

namespace L1Coordinates

variable {K I H : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H]

local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (Words I) := Classical.decEq _

/-- The power series of `g`, made of the multilinear word blocks.-/
def wordSeries (s : K) : FormalMultilinearSeries K (L1 K I) (L1 K (Words I)) :=
  wordBlock s

end L1Coordinates
