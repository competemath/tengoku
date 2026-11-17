import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.FlagAdiacente
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 12 — IL LINGUAGGIO DELLE GALLERIE (19 lug 2026).

La mossa elementare (`FlagStep`) e la connessione per gallerie
(`GalleryConnected`, chiusura riflessivo-transitiva). Qui i lemmi
strutturali: la mossa è simmetrica, la connessione è un'equivalenza,
e l'azione delle simmetrie la rispetta. Il teorema profondo — OGNI due
bandiere sono connesse — è il muro successivo e vivrà in un modulo suo.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La mossa elementare: `G` differisce da `F` in un solo rango.-/
def FlagStep (P : ConvexPolytope n) (F G : P.Flag) : Prop :=
  ∃ i : Fin n, FlagAdjacentAt P F G i

/-- Connessione per gallerie: una catena finita di mosse elementari.-/
def GalleryConnected (P : ConvexPolytope n) (F G : P.Flag) : Prop :=
  Relation.ReflTransGen (FlagStep P) F G

/-- La mossa elementare è simmetrica.-/
theorem flagStep_symm (P : ConvexPolytope n) {F G : P.Flag}
    (h : FlagStep P F G) : FlagStep P G F := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, flagAdjacentAt_symm P hi⟩

/-- Le simmetrie trasportano mosse in mosse.-/
theorem flagStep_map (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) {F G : P.Flag} (h : FlagStep P F G) :
    FlagStep P (mapFlag P hφ F) (mapFlag P hφ G) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, flagAdjacentAt_map P hφ hi⟩

end LeanEval.Geometry.PlatonicClassification
