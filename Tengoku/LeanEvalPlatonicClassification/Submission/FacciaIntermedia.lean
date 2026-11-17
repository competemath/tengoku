import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.SottoPolitopo
import Tengoku.LeanEvalPlatonicClassification.Submission.Interpolazione
import Tengoku.LeanEvalPlatonicClassification.Submission.DimStretta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 1 — LA FACCIA INTERMEDIA ESISTE (19 lug 2026).

Il lato «almeno uno» del diamante in rango arbitrario, ottenuto SENZA
teoria nuova: la relativizzazione era già nell'infrastruttura. Il
sotto-politopo di una faccia (`facePolytope`) ha per corpo la faccia
stessa, eredita le facce nei due versi, e `interpolazione` non chiede la
piena dimensionalità nell'ambiente ma lavora sulla dimensione intrinseca
`finrank (vectorSpan toSet)`. Dunque, date `A ⊂ B` con salto di rango 2:
si scende nel sotto-politopo di `B`, si interpola, si risale.

Correzione del vaglio avversariale accolta: questo è il lato facile; il
kill-gate vero («esattamente due») è un teorema separato.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

end LeanEval.Geometry.PlatonicClassification
