import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.FiguraAlVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Gallerie

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
LA MACCHINA DELLE BANDIERE (21 lug 2026) — Wythoff end-node, forma magra.

Per dimostrare che un politopo è regolare NON serve la geometria dei coset
parabolici: bastano le `n` RIFLESSIONI-PARETE di una sola bandiera
fondamentale.  Il resto lo fa `galleryConnected_sempre` (incondizionato,
caduto stanotte): ogni bandiera è collegata alla fondamentale da una
galleria, e l'induzione lungo la galleria — con l'equivarianza
`mapFlag_adjacentFlag` — produce la simmetria che la raggiunge, componendo
una riflessione-parete per passo.  Le facce «supplementari» non vanno
escluse: la galleria le attraversa per costruzione.

Interfaccia per i modelli (24-cell, 600-cell, 120-cell): esibire una
bandiera `Φ₀` e, per ogni rango `i`, un'isometria `r i` che preserva il
politopo ed è `i`-adiacente a `Φ₀` (`FlagAdjacentAt`: fissa le facce di
rango `j ≠ i`, muove quella di rango `i`).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'identità è una simmetria.-/
theorem isSymmetry_refl (P : ConvexPolytope n) :
    P.isSymmetry (AffineIsometryEquiv.refl ℝ (E n)) := by
  rw [ConvexPolytope.isSymmetry]
  simp

/-- L'identità agisce banalmente sulle bandiere.-/
theorem mapFlag_refl (P : ConvexPolytope n) (F : P.Flag) :
    mapFlag P (isSymmetry_refl P) F = F := by
  apply flag_ext
  funext k
  show (⇑(AffineIsometryEquiv.refl ℝ (E n))) '' F.face k = F.face k
  simp

end LeanEval.Geometry.PlatonicClassification
