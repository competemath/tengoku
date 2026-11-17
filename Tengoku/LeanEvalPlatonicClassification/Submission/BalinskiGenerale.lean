import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.PernoMonotono
import Tengoku.LeanEvalPlatonicClassification.Submission.OrbitaVertici
import Tengoku.LeanEvalPlatonicClassification.Submission.ConoVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.Camminata

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
BALINSKI-LIGHT IN DIMENSIONE ARBITRARIA (20 lug 2026).

Il grafo degli estremi di un politopo convesso finito è connesso, anche
quando il politopo non è pieno nell'ambiente.  Il passo locale è il pivot
monotono: se un funzionale cresce verso qualche vertice, il primo tempo
critico produce una faccia più grande della zero-faccia corrente e tutti
i suoi punti nuovi migliorano il funzionale.  Una catena radicata estrae
da tale faccia uno spigolo uscente.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Relazione orientata usata dalla camminata: il punto di arrivo è un
vertice e i due punti sono gli estremi distinti di uno spigolo comune.-/
def GeneralVertexStep (P : ConvexPolytope n) (p q : E n) : Prop :=
  q ∈ P.vertices ∧ p ≠ q ∧
    ∃ e : Set (E n), P.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e

end LeanEval.Geometry.PlatonicClassification
