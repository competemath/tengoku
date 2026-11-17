import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.LibertaGenerica

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 14 — IL GRUPPO DI SIMMETRIA È FINITO (19 lug 2026).

Conseguenza diretta della libertà: l'azione delle simmetrie sulle
bandiere è libera, dunque l'orbita di una bandiera base distingue le
simmetrie. Poiché le facce di un politopo sono in numero finito, le
bandiere lo sono, e con esse il gruppo.

È il fatto che rende sensato parlare di ORDINE dei prodotti `rᵢ rⱼ`:
in un gruppo finito ogni elemento ha ordine finito, e la matrice di
Coxeter esiste.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- **Le bandiere sono in numero finito**: una bandiera è determinata
dalla sua catena, e le facce sono finite.-/
theorem flag_finite (P : ConvexPolytope n) : Finite P.Flag := by
  haveI : Finite {f : Set (E n) // P.IsFace f} :=
    Set.Finite.to_subtype (facce_finite P)
  refine Finite.of_injective
    (f := fun F : P.Flag =>
      (fun k : Fin n => (⟨F.face k, F.isFace k⟩ : {f : Set (E n) // P.IsFace f})))
    ?_
  intro F G h
  apply flag_ext
  funext k
  have hk := congrFun h k
  exact congrArg Subtype.val hk

end LeanEval.Geometry.PlatonicClassification
