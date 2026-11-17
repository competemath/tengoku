import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Interpolazione

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
PERNO MONOTONO (20 lug 2026).

È la variante orientata del perno finito: se un funzionale `h` cresce da
una faccia esposta `f` verso almeno un vertice, al primo tempo critico si
ottiene una faccia più grande `f'`; inoltre ogni punto nuovo di `f'` ha
valore di `h` strettamente maggiore del valore (costante) su `f`.

Quest'ultima clausola, assente dalla firma storica di
`perno_parametrico_crescente`, è ciò che permette il pivot monotono del
grafo dei vertici in dimensione arbitraria.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

end LeanEval.Geometry.PlatonicClassification
