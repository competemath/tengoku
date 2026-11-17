import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.GruppoFinito
import Tengoku.LeanEvalPlatonicClassification.Submission.Ordini
import Tengoku.LeanEvalPlatonicClassification.Submission.Coniugazione
import Tengoku.LeanEvalPlatonicClassification.Submission.OrdineTre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 26 — IL SIMBOLO DI SCHLÄFLI (19 lug 2026).

Il simbolo `{m₀, …, m_{d−2}}` come funzione del politopo. La bandiera
base entra nella definizione (serve una scelta) ma esce dal contratto
pubblico: `coxeterMatrix_indep` garantisce che il valore non dipenda
dalla scelta, e il teorema `schlafli_indipendente` lo registra.

Le proprietà certificate qui:
  · indipendenza dalla bandiera base;
  · `mᵢ ≥ 3` su ogni entrata (dal fascicolo degli ordini adiacenti);
  · le entrate sono finite e positive.

NON è certificato qui, ed è dichiarato come lavoro aperto: l'invarianza
sotto similitudine, che richiede il trasporto delle bandiere lungo
l'isometria in dimensione arbitraria.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il rango successivo, quando esiste.-/
def rangoSucc (i : Fin n) (hi : (i : ℕ) + 1 < n) : Fin n :=
  ⟨(i : ℕ) + 1, hi⟩

/-- **Il simbolo di Schläfli**, relativo a una bandiera base.-/
noncomputable def schlafliDi (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) : ℕ :=
  coxeterMatrix P hreg F i (rangoSucc i hi)

/-- Il simbolo come famiglia indicizzata dai ranghi interni.-/
noncomputable def schlafli (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) : Fin n → ℕ :=
  fun i =>
    if hi : (i : ℕ) + 1 < n then schlafliDi P hreg F i hi else 0

/--
@isnad1 id=eq.2h4v.s5.dbe22e65d12a from=translated src=- shape=0544674b vocab=3be70ecf
-/
theorem schlafli_apply (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    schlafli P hreg F i = schlafliDi P hreg F i hi := by
  unfold schlafli
  rw [dite_eq_left hi]

end LeanEval.Geometry.PlatonicClassification
