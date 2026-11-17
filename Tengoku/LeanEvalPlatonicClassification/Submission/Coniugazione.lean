import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.LibertaGenerica
import Tengoku.LeanEvalPlatonicClassification.Submission.GruppoFinito
import Tengoku.LeanEvalPlatonicClassification.Submission.Ordini

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 16 — CONIUGAZIONE E INDIPENDENZA DALLA BASE
(19 lug 2026).

Cambiare bandiera base coniuga i generatori: `r'ᵢ = g rᵢ g⁻¹`, dove `g`
è il trasportatore. Ne segue che la matrice di Coxeter NON dipende dalla
bandiera scelta: è un invariante del politopo.

Il perno è l'unicità del trasportatore, a sua volta conseguenza della
libertà dell'azione.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'azione del gruppo di simmetria sulle bandiere.-/
noncomputable def act (P : ConvexPolytope n) (g : symGroup P) (F : P.Flag) :
    P.Flag :=
  mapFlag P g.2 F

@[simp] theorem act_face (P : ConvexPolytope n) (g : symGroup P)
    (F : P.Flag) (k : Fin n) :
    (act P g F).face k = (⇑(g : Isom n)) '' F.face k := rfl

theorem act_one (P : ConvexPolytope n) (F : P.Flag) :
    act P 1 F = F := by
  apply flag_ext
  funext k
  show (⇑((1 : symGroup P) : Isom n)) '' F.face k = F.face k
  simp

theorem act_mul (P : ConvexPolytope n) (a b : symGroup P) (F : P.Flag) :
    act P (a * b) F = act P a (act P b F) := by
  apply flag_ext
  funext k
  show (⇑((a * b : symGroup P) : Isom n)) '' F.face k =
    (⇑(a : Isom n)) '' ((⇑(b : Isom n)) '' F.face k)
  rw [Set.image_image]
  rfl

/-- L'azione commuta con la mossa di adiacenza.-/
theorem act_adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (g : symGroup P) (F : P.Flag) (i : Fin n) :
    act P g (adjacentFlag P hfull F i) =
      adjacentFlag P hfull (act P g F) i :=
  mapFlag_adjacentFlag P hfull g.2 F i

/-- Il generatore, applicato alla propria bandiera base, dà l'adiacente.-/
theorem act_simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    act P (simpleGen P hreg F i) F = adjacentFlag P hreg.1 F i :=
  simpleReflection_mapFlag P hreg F i

/-- Il trasportatore come elemento del gruppo.-/
noncomputable def transp (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : symGroup P :=
  ⟨transporter P hreg F G, transporter_isSymmetry P hreg F G⟩

theorem act_transp (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : act P (transp P hreg F G) F = G :=
  transporter_mapFlag P hreg F G

end LeanEval.Geometry.PlatonicClassification
