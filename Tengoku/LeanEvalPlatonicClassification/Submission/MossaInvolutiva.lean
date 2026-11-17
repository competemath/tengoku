import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.FlagAdiacente
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 7 — LA MOSSA INVOLUTIVA (19 lug 2026).

Dal teorema di unicità l'adiacenza diventa una FUNZIONE sulle bandiere:
`adjacentFlag P hfull F i` è l'unica bandiera adiacente a `F` in `i`.
La relazione è simmetrica, quindi la mossa è un'involuzione senza punti
fissi: il germe combinatorio delle riflessioni semplici `rᵢ² = 1`.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La bandiera adiacente a `F` al rango `i` (l'unica).-/
noncomputable def adjacentFlag (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) : P.Flag :=
  (existsUnique_flag_adjacent P hfull F i).choose

/--
@isnad1 id=flagadja.1h4v.s4.bebaf48f52c2 from=translated src=- shape=0c3f97b7 vocab=34b15869
-/
theorem adjacentFlag_isAdjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    FlagAdjacentAt P F (adjacentFlag P hfull F i) i :=
  (existsUnique_flag_adjacent P hfull F i).choose_spec.1

/-- Ogni bandiera adiacente a `F` in `i` È la bandiera adiacente.
@isnad1 id=eq.2h5v.s5.0db516df0e55 from=translated src=- shape=a2566529 vocab=34b15869
-/
theorem adjacentFlag_eq_of_isAdjacent (P : ConvexPolytope n)
    (hfull : P.IsFullDim) {F G : P.Flag} (i : Fin n)
    (h : FlagAdjacentAt P F G i) : G = adjacentFlag P hfull F i :=
  (existsUnique_flag_adjacent P hfull F i).choose_spec.2 G h

/-- L'adiacenza di bandiere è simmetrica.
@isnad1 id=flagadja.1h5v.s4.dd0490053c1f from=translated src=- shape=e3dcc72d vocab=971804e7
-/
theorem flagAdjacentAt_symm (P : ConvexPolytope n) {F G : P.Flag}
    {i : Fin n} (h : FlagAdjacentAt P F G i) :
    FlagAdjacentAt P G F i :=
  ⟨fun j hj => (h.1 j hj).symm, (h.2).symm⟩

/-- **La mossa è un'involuzione**: andare e tornare riporta a `F`.
@isnad1 id=eq.1h4v.s5.8ec4a903ee89 from=translated src=- shape=37b7484d vocab=4c987ca4
-/
theorem adjacentFlag_involutive (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    adjacentFlag P hfull (adjacentFlag P hfull F i) i = F :=
  (adjacentFlag_eq_of_isAdjacent P hfull i
    (flagAdjacentAt_symm P (adjacentFlag_isAdjacent P hfull F i))).symm

/-- La mossa non ha punti fissi.
@isnad1 id=ne.1h4v.s4.d9342262bd16 from=translated src=- shape=e0a42025 vocab=4c987ca4
-/
theorem adjacentFlag_ne (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (F : P.Flag) (i : Fin n) :
    adjacentFlag P hfull F i ≠ F := by
  intro heq
  have h := (adjacentFlag_isAdjacent P hfull F i).2
  rw [heq] at h
  exact h rfl

end LeanEval.Geometry.PlatonicClassification
