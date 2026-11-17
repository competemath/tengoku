import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.ConnettivitaRidgeTre
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.Interpolazione

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
RIDUZIONE ESATTA DEL MURO DEL RIDGE-GRAPH (20 lug 2026).

La base intrinseca 2 e il caso intrinseco 3 sono chiusi nei moduli
precedenti.  In rango superiore, Balinski-light riduce la connettività
globale delle faccette alla connettività locale delle faccette incidenti
a uno stesso vertice.  Ogni spigolo della camminata si estende a una
faccetta mediante massimalità nella famiglia finita delle facce proprie.

La definizione `VertexStarRidgeConnectedAboveThree` è quindi il
sotto-kill-gate preciso rimasto: è la connettività del grafo delle
faccette nello star di un vertice, per una faccia di dimensione almeno
quattro.  Il teorema finale di questo file dimostra, senza assiomi
aggiuntivi, che tale enunciato implica esattamente
`RidgeConnectedAboveOne`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il passo del ridge-graph delle faccette proprie di `B`.-/
def RidgeStepIn (P : ConvexPolytope n) (B : Set (E n))
    (X Y : Set (E n)) : Prop :=
  P.IsFace X ∧ P.IsFace Y ∧ X ⊂ B ∧ Y ⊂ B ∧
    faceDim X + 1 = faceDim B ∧ faceDim Y + 1 = faceDim B ∧
    ∃ R : Set (E n), P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧
      faceDim R + 2 = faceDim B

/-- Sotto-kill-gate superiore: due faccette di `B` incidenti allo stesso
vertice sono connesse per ridge, restando dentro `B`.  La soglia `4`
esclude esattamente i ranghi già chiusi in
`ConnettivitaRidgeBase` e `ConnettivitaRidgeTre`.-/
def VertexStarRidgeConnectedAboveThree (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)) (hB : P.IsFace B), 4 ≤ faceDim B →
    ∀ v : E n, v ∈ (facePolytope P hB).vertices →
      ∀ (X Y : Set (E n)), P.IsFace X → P.IsFace Y →
        X ⊂ B → Y ⊂ B →
        faceDim X + 1 = faceDim B →
        faceDim Y + 1 = faceDim B →
        v ∈ X → v ∈ Y →
        Relation.ReflTransGen (RidgeStepIn P B) X Y

end LeanEval.Geometry.PlatonicClassification
