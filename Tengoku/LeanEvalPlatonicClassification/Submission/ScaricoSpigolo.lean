import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.Diamante
import Tengoku.LeanEvalPlatonicClassification.Submission.FanVertice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FASE 3A — SCARICO DI `EdgeInAtMostTwoFacets` (18 lug 2026).

Il predicato locale assunto dal gemello KG-3A2 vale INCONDIZIONATAMENTE:
è esattamente la forma quantificata del diamante.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **Il lemma locale del fan è un teorema**: in ogni politopo di ℝ³, per
ogni punto `v`, uno spigolo sta in al più due faccette.
@isnad1 id=edgeinat.0h2v.s4.b63851b0899e from=translated src=- shape=1a1b9d4f vocab=4245018e
-/
theorem edgeInAtMostTwoFacets_vale (P : ConvexPolytope 3) (v : E 3) :
    ConvexPolytope.EdgeInAtMostTwoFacets P v := by
  intro A B C hA hdA hB hdB hC hdC hAB hvA hvB hvC x hx hxv hxC
  exact spigolo_in_due_faccette P v hA hdA hB hdB hC hdC hAB hvA hvB hvC
    hx hxv hxC

end LeanEval.Geometry.PlatonicClassification
