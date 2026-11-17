import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.DimStretta
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Gallerie

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 17 — INFRASTRUTTURA DELLE GALLERIE E IL MURO
(19 lug 2026).

Il muro grande del motore resta la connettività: che ogni due bandiere
siano collegate da una galleria. Qui NON lo si dimostra. Si certifica
l'infrastruttura che servirà alla dimostrazione, e si scrive il muro
nella sua forma corretta, che è locale e più debole della tesi:

`RidgeConnected P` — dentro ogni faccia `B`, due facce di codimensione 1
sono collegate da una catena in cui consecutive si incontrano in una
faccia di codimensione 2. È la connettività del grafo delle faccette
(Balinski in forma debole), il fatto geometrico da cui la connettività
per gallerie discende per induzione sul rango.

Attenzione a non confondere questo con l'enunciato «due bandiere che
coincidono sopra il rango massimo sono connesse», che è vacuo: coincidere
sopra `n − 1` non è un'ipotesi, è la tesi generale travestita.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Due bandiere coincidono dal rango `m` in su.-/
def AgreeAbove (P : ConvexPolytope n) (F G : P.Flag) (m : ℕ) : Prop :=
  ∀ k : Fin n, m ≤ (k : ℕ) → F.face k = G.face k

/--
@isnad1 id=eq.1h4v.s4.a233aecee2cd from=translated src=- shape=ee5ce611 vocab=dcfab4d9
-/
theorem agreeAbove_zero (P : ConvexPolytope n) {F G : P.Flag}
    (h : AgreeAbove P F G 0) : F = G := by
  apply flag_ext
  funext k
  exact h k (Nat.zero_le _)

/--
@isnad1 id=agreeabo.2h6v.s5.6f222787e74a from=translated src=- shape=6fe8ee79 vocab=4daeadf6
-/
theorem agreeAbove_mono (P : ConvexPolytope n) {F G : P.Flag} {m m' : ℕ}
    (hmm : m ≤ m') (h : AgreeAbove P F G m) : AgreeAbove P F G m' :=
  fun k hk => h k (le_trans hmm hk)

/-- Sopra il rango massimo l'ipotesi è vuota: `AgreeAbove _ _ n` non dice
nulla. Registrato esplicitamente per non scambiarlo per un'induzione.
@isnad1 id=agreeabo.1h5v.s4.e1db57707a2c from=translated src=- shape=5caec2df vocab=4daeadf6
-/
theorem agreeAbove_of_ge (P : ConvexPolytope n) (F G : P.Flag) {m : ℕ}
    (hm : n ≤ m) : AgreeAbove P F G m := by
  intro k hk
  exfalso
  have := k.isLt
  omega

/-- Bandiere adiacenti coincidono sopra il rango della mossa più uno.
@isnad1 id=agreeabo.1h5v.s5.d71f97655f99 from=translated src=- shape=0fa71882 vocab=1a378815
-/
theorem agreeAbove_of_adjacent (P : ConvexPolytope n) {F G : P.Flag}
    {i : Fin n} (h : FlagAdjacentAt P F G i) :
    AgreeAbove P F G ((i : ℕ) + 1) := by
  intro k hk
  refine (h.1 k (fun hki => ?_)).symm
  rw [hki] at hk
  omega

/-- **IL MURO, in forma locale.** Dentro ogni faccia `B`, due facce di
codimensione 1 in `B` sono collegate da una catena di facce di
codimensione 1 in cui due consecutive si incontrano in una faccia di
codimensione 2. È la connettività del grafo delle faccette.-/
def RidgeConnected (P : ConvexPolytope n) : Prop :=
  ∀ (B : Set (E n)), P.IsFace B →
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
