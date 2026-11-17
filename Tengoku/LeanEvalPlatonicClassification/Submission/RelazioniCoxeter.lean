import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.FlagAdiacente
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.Commutazione
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioneLontana
import Tengoku.LeanEvalPlatonicClassification.Submission.LibertaGenerica

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 13 — LE RELAZIONI NEL GRUPPO (19 lug 2026).

La libertà dell'azione (`bandiera_fissata_id`) promuove le identità di
BANDIERE già certificate a identità di ISOMETRIE. Le due prime famiglie
di relazioni di Coxeter sono qui:

    rᵢ² = 1                    (le riflessioni sono involuzioni)
    (rᵢ rⱼ)² = 1  se |i−j| ≥ 2 (i generatori lontani commutano)

Il ponte è sempre lo stesso: una composizione di simmetrie che fissa
tutte le facce della bandiera base è l'identità.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'immagine lungo una composizione è la composizione delle immagini.
@isnad1 id=eq.0h4v.s11.ca4539d8319f from=translated src=- shape=2712a6dc vocab=bf4a9681
-/
theorem image_trans_isom (φ ψ : Isom n) (S : Set (E n)) :
    (⇑(φ.trans ψ)) '' S = (⇑ψ) '' ((⇑φ) '' S) := by
  rw [Set.image_image]
  rfl

/-- Le riflessioni semplici non sono l'identità.
@isnad1 id=not.1h4v.s8.5cfe8737dad4 from=translated src=- shape=f14b5e0f vocab=331009a5
-/
theorem simpleReflection_ne_id (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    ¬ (∀ x : E n, simpleReflection P hreg F i x = x) := by
  intro hid
  have hflag : mapFlag P (simpleReflection_isSymmetry P hreg F i) F = F := by
    apply flag_ext
    funext k
    show (⇑(simpleReflection P hreg F i)) '' F.face k = F.face k
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [hid z]
    · intro hy
      exact ⟨y, hy, hid y⟩
  have hne := adjacentFlag_ne P hreg.1 F i
  rw [← simpleReflection_mapFlag P hreg F i] at hne
  exact hne hflag

end LeanEval.Geometry.PlatonicClassification
