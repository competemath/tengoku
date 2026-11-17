import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.PerturbazioneFinita
import Tengoku.LeanEvalPlatonicClassification.Submission.VerticiEsposti
import Tengoku.LeanEvalPlatonicClassification.Submission.SottoPolitopo

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FASE 3A, Q3-S1 — IL PERNO (18 lug 2026).

Sopra ogni faccia propria di un politopo c'è una faccia strettamente più
grande.  Il secondo funzionale è costruito col residuo ortogonale rispetto
alla direzione affine della faccia; il tempo di perturbazione è il minimo
dei rapporti critici sui vertici sui quali quel funzionale cresce.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

end LeanEval.Geometry.PlatonicClassification
