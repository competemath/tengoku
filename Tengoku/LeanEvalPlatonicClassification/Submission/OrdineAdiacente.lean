import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter
import Tengoku.LeanEvalPlatonicClassification.Submission.GruppoFinito
import Tengoku.LeanEvalPlatonicClassification.Submission.Ordini
import Tengoku.LeanEvalPlatonicClassification.Submission.Coniugazione
import Tengoku.LeanEvalPlatonicClassification.Submission.TreIntermedie
import Tengoku.LeanEvalPlatonicClassification.Submission.FaccetteConnesse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 22 — GLI ORDINI ADIACENTI SONO ALMENO 3
(19 lug 2026).

Con la connettività del residuo (caduta col fascicolo 45), il gruppo
`⟨μᵢ, μᵢ₊₁⟩` agisce transitivamente sulle bandiere del residuo. Se
`mᵢ` fosse 2, le due mosse commuterebbero e l'orbita della bandiera base
conterrebbe al più QUATTRO bandiere, con al più DUE facce distinte al
rango `i`. Ma l'intervallo di rango 3 ne contiene almeno tre
(`tre_intermedie_di_rango_tre`), e per connettività ogni faccia del
residuo compare nell'orbita. Contraddizione.

Il cuore è il lemma di orbita: percorrendo una galleria del residuo, la
faccia di rango `i` raggiunta è sempre una di quelle che compaiono nelle
bandiere generate dalle due mosse.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

end LeanEval.Geometry.PlatonicClassification
