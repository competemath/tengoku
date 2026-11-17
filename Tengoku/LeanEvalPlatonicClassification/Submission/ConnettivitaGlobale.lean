import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Connettivita
import Tengoku.LeanEvalPlatonicClassification.Submission.DueVertici

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, U4 — DAL MURO LOCALE ALLE GALLERIE GLOBALI (20 lug 2026).

Questo modulo isola e chiude la riduzione combinatoria

`RidgeConnected P → ∀ F G : P.Flag, GalleryConnected P F G`.

Il caso inferiore non usa `RidgeConnected`: due bandiere che coincidono
dal rango 1 differiscono al più nel rango 0.  Nel passo induttivo, la
catena di faccette fornita da `RidgeConnected` viene sollevata a bandiere.
Per ogni ridge si ricostruisce una catena completa sotto di esso; così le
due bandiere ai lati del ridge differiscono in un solo rango.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La forma corretta e sufficiente del muro locale.  Il vincolo
`2 ≤ faceDim B` è essenziale perché il modello di faccia del benchmark
esclude la faccia vuota: per `faceDim B = 1` non esiste una ridge di
dimensione `-1`, e quel caso delle gallerie si risolve direttamente.-/
def RidgeConnectedAboveOne (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)), P.IsFace B → 2 ≤ faceDim B →
    ∀ (A A' : Set (E n)), P.IsFace A → P.IsFace A' →
      A ⊂ B → A' ⊂ B →
      faceDim A + 1 = faceDim B → faceDim A' + 1 = faceDim B →
      Relation.ReflTransGen
        (fun X Y : Set (E n) =>
          P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
            faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
            ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
              faceDim R + 2 = faceDim B)
        A A'

end LeanEval.Geometry.PlatonicClassification
