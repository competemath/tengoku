import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.Gallerie
import Tengoku.LeanEvalPlatonicClassification.Submission.LibertaGenerica
import Tengoku.LeanEvalPlatonicClassification.Submission.GruppoFinito
import Tengoku.LeanEvalPlatonicClassification.Submission.Ordini
import Tengoku.LeanEvalPlatonicClassification.Submission.Coniugazione

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 21 — LE RIFLESSIONI SEMPLICI GENERANO IL GRUPPO
(19 lug 2026).

Secondo ramo del diagramma: dalla connettività per gallerie discende che
ogni simmetria del politopo è una PAROLA nelle riflessioni semplici.

Il passo induttivo è più semplice di quanto sembri, e non richiede
coniugazioni: percorrendo una galleria, l'equivarianza fa scivolare la
mossa dall'estremità raggiunta alla bandiera base, e la parola cresce
semplicemente a destra,

    act (w · rᵢ) F = adj_i (act w F).

L'ipotesi di connettività è ESPLICITA nella firma: non è assunta di
nascosto. Quando il muro (connettività dei residui e delle gallerie)
cadrà, questo teorema si scaricherà da sé.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il sottogruppo generato dalle riflessioni semplici, relativo a una
bandiera base.-/
def simpleSubgroup (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : Subgroup (symGroup P) :=
  Subgroup.closure (Set.range (simpleGen P hreg F))

/--
@isnad1 id=mem.1h4v.s11.67780cde8b3e from=translated src=- shape=f4a1ac82 vocab=7a82adf8
-/
theorem simpleGen_mem (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    simpleGen P hreg F i ∈ simpleSubgroup P hreg F :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Il passo che fa crescere la parola: moltiplicare a destra per `rᵢ`
equivale a fare la mossa `i` sulla bandiera raggiunta.
@isnad1 id=eq.1h5v.s11.0e809fdd538a from=translated src=- shape=0bfc5949 vocab=e4b9cbee
-/
theorem act_mul_simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (w : symGroup P) (i : Fin n) :
    act P (w * simpleGen P hreg F i) F =
      adjacentFlag P hreg.1 (act P w F) i := by
  rw [act_mul, act_simpleGen P hreg F i]
  exact act_adjacentFlag P hreg.1 w F i

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
