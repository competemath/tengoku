import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter
import Tengoku.LeanEvalPlatonicClassification.Submission.Ordini
import Tengoku.LeanEvalPlatonicClassification.Submission.Coniugazione
import Tengoku.LeanEvalPlatonicClassification.Submission.TreIntermedie
import Tengoku.LeanEvalPlatonicClassification.Submission.FaccetteConnesse
import Tengoku.LeanEvalPlatonicClassification.Submission.OrdineAdiacente
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraDelResiduo
import Tengoku.LeanEvalPlatonicClassification.Submission.PonteMosse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 24 — GLI ORDINI ADIACENTI SONO ALMENO 3
(19 lug 2026).

Il montaggio finale. Se `mᵢ,ᵢ₊₁ = 2`:

  ordine 2  →  le riflessioni commutano nel gruppo      (`simpleGen_comm_of_order_two`)
            →  le MOSSE commutano sulle bandiere         (`mosse_commutano_di_riflessioni`)
            →  l'orbita ha ≤ 4 bandiere                  (`residuo_chiuso_di_commutazione`)
            →  ≤ 2 facce distinte al rango i             (`facce_del_residuo_chiuso`)

mentre dall'altro lato:

  intervallo di rango 3  →  ≥ 3 facce intermedie distinte (`tre_intermedie_di_rango_tre`)
                         →  ciascuna sta in una bandiera del residuo (`bandiera_del_residuo_generale`)
                         →  ciascuna bandiera è raggiungibile          (`residuo_rango_tre_connesso`)

Tre facce distinte non stanno in un insieme di due.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

end LeanEval.Geometry.PlatonicClassification
