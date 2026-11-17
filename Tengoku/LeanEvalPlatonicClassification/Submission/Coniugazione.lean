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

/--
@isnad1 id=eq.0h5v.s10.e62b2439aa8f from=translated src=- shape=7e21c8da vocab=44433e11
-/
@[simp] theorem act_face (P : ConvexPolytope n) (g : symGroup P)
    (F : P.Flag) (k : Fin n) :
    (act P g F).face k = (⇑(g : Isom n)) '' F.face k := rfl

/--
@isnad1 id=eq.0h3v.s10.3221d263c2e6 from=translated src=- shape=a7366107 vocab=a2b65b45
-/
theorem act_one (P : ConvexPolytope n) (F : P.Flag) :
    act P 1 F = F := by
  apply flag_ext
  funext k
  show (⇑((1 : symGroup P) : Isom n)) '' F.face k = F.face k
  simp

/--
@isnad1 id=eq.0h5v.s11.5b9c385d3466 from=translated src=- shape=34df250d vocab=bdbf3904
-/
theorem act_mul (P : ConvexPolytope n) (a b : symGroup P) (F : P.Flag) :
    act P (a * b) F = act P a (act P b F) := by
  apply flag_ext
  funext k
  show (⇑((a * b : symGroup P) : Isom n)) '' F.face k =
    (⇑(a : Isom n)) '' ((⇑(b : Isom n)) '' F.face k)
  rw [Set.image_image]
  rfl

/-- L'azione commuta con la mossa di adiacenza.
@isnad1 id=eq.1h5v.s9.d1ba0ccd8b77 from=translated src=- shape=af4bb765 vocab=68dd5baf
-/
theorem act_adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (g : symGroup P) (F : P.Flag) (i : Fin n) :
    act P g (adjacentFlag P hfull F i) =
      adjacentFlag P hfull (act P g F) i :=
  mapFlag_adjacentFlag P hfull g.2 F i

/-- Il generatore, applicato alla propria bandiera base, dà l'adiacente.
@isnad1 id=eq.1h4v.s5.2c0ee29bb793 from=translated src=- shape=975203fc vocab=11f94b8d
-/
theorem act_simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) :
    act P (simpleGen P hreg F i) F = adjacentFlag P hreg.1 F i :=
  simpleReflection_mapFlag P hreg F i

/-- Il trasportatore come elemento del gruppo.-/
noncomputable def transp (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : symGroup P :=
  ⟨transporter P hreg F G, transporter_isSymmetry P hreg F G⟩

/--
@isnad1 id=eq.1h4v.s5.6870bc7d9af6 from=translated src=- shape=c606adc2 vocab=36951064
-/
theorem act_transp (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F G : P.Flag) : act P (transp P hreg F G) F = G :=
  transporter_mapFlag P hreg F G

end LeanEval.Geometry.PlatonicClassification
