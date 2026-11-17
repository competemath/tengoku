import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.FlagAdiacente
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.Commutazione

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 11 — LA RELAZIONE LONTANA SULLE BANDIERE
(19 lug 2026).

Per ranghi non adiacenti (`i + 2 ≤ j`) il prodotto `rᵢ rⱼ` applicato due
volte fissa la bandiera base: il calcolo insegue le quattro applicazioni
attraverso l'equivarianza, riduce con la commutazione delle mosse e
chiude con l'involutività. Ogni ingrediente è già certificato; quando la
libertà dell'azione sarà in cassaforte, questo enunciato si promuoverà
alla relazione di Coxeter `(rᵢ rⱼ)² = 1` nel gruppo di simmetria.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **La relazione lontana sulle bandiere**: per `i + 2 ≤ j`,
`rᵢ rⱼ rᵢ rⱼ` riporta la bandiera base in sé.
@isnad1 id=eq.2h5v.s6.bf30f5940e6e from=translated src=- shape=2298f9c5 vocab=5f492121
-/
theorem simpleReflection_far_comm_fixes (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) {i j : Fin n}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ)) :
    mapFlag P (simpleReflection_isSymmetry P hreg F i)
      (mapFlag P (simpleReflection_isSymmetry P hreg F j)
        (mapFlag P (simpleReflection_isSymmetry P hreg F i)
          (mapFlag P (simpleReflection_isSymmetry P hreg F j) F))) = F := by
  rw [simpleReflection_mapFlag P hreg F j,
    mapFlag_adjacentFlag P hreg.1
      (simpleReflection_isSymmetry P hreg F i) F j,
    simpleReflection_mapFlag P hreg F i,
    mapFlag_adjacentFlag P hreg.1
      (simpleReflection_isSymmetry P hreg F j)
      (adjacentFlag P hreg.1 F i) j,
    mapFlag_adjacentFlag P hreg.1
      (simpleReflection_isSymmetry P hreg F j) F i,
    simpleReflection_mapFlag P hreg F j,
    adjacentFlag_comm P hreg.1 F hij,
    adjacentFlag_involutive P hreg.1 (adjacentFlag P hreg.1 F i) j]
  exact simpleReflection_swaps P hreg F i

end LeanEval.Geometry.PlatonicClassification
