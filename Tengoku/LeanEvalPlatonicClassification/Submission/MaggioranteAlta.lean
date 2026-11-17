import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.ConteggioBenchmark
import Tengoku.LeanEvalPlatonicClassification.Submission.SimilarEquiv
import Tengoku.LeanEvalPlatonicClassification.Submission.LowerBoundFinale
import Tengoku.LeanEvalPlatonicClassification.Submission.Simplesso
import Tengoku.LeanEvalPlatonicClassification.Submission.Ortoplesse
import Tengoku.LeanEvalPlatonicClassification.Submission.OrtoplesseFacce
import Tengoku.LeanEvalPlatonicClassification.Submission.Ipercubo

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
RIGIDITÀ ALTA — IL MAGGIORANTE E L'EQUAZIONE FINALE d≥5 (21 lug 2026).

Il minorante `3 ≤ platonicCount d` è già scaricato e INCONDIZIONATO
(`three_le_platonicCount`, LowerBoundFinale — simplesso, ortoplesse,
ipercubo).  Qui la controparte: se ogni politopo regolare di ℝᵈ è simile a
uno dei TRE testimoni (LA RIGIDITÀ d≥5, in scarico via l'unicità: esclusività
`schlafli_high_dim_exclusive` + registrazione U1/U2 + vertice seme + orbita
U4, con l'ultimo sotto-gate `VertexStarRidgeConnectedAboveThree`), allora le
classi sono al più tre, e con il minorante `platonicCount d = 3`.

L'intera campagna d≥5 si riduce così a scaricare UNA ipotesi:
`∀ P : regularPolytopes d, ∃ i : Fin 3, regularSimilar d P (testimoneAlto d hd1 i)`.

Questo modulo è INDIPENDENTE dal sotto-gate: fornisce l'incastro finale.
Copia verificata del pattern `Maggiorante.lean` (dim 3, Fin 5) a `Fin 3`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- I tre testimoni regolari in dimensione `d`: simplesso, ortoplesse,
ipercubo.  Ognuno è `IsRegular` in ogni `d ≥ 1` (LowerBoundFinale).-/
def testimoneAlto (d : ℕ) (hd : 1 ≤ d) : Fin 3 → regularPolytopes d :=
  ![⟨simplesso d hd, simplesso_mem_regularPolytopes d hd⟩,
    ⟨ortoplesse d hd, ortoplesse_mem_regularPolytopes d hd⟩,
    ⟨ipercubo d hd, ipercubo_mem_regularPolytopes d hd⟩]

/-- Simili ⟹ stessa classe (versione dimension-free).
@isnad1 id=eq.1h3v.s5.6a25db73f387 from=translated src=- shape=bd8ab2af vocab=cd9ae297
-/
theorem classe_eq_of_similar_gen {d : ℕ} {P Q : regularPolytopes d}
    (h : regularSimilar d P Q) : classe d P = classe d Q := by
  ext R
  constructor
  · intro hR
    exact similar_trans (similar_symm h) hR
  · intro hR
    exact similar_trans h hR

/-- **IL MAGGIORANTE CONDIZIONALE d≥5**: se ogni regolare è simile a un
testimone, le classi sono al più tre.
@isnad1 id=le.2h1v.s5.2368b08b7253 from=translated src=- shape=45a2678a vocab=732a6632
-/
theorem platonicCount_le_tre_di {d : ℕ} (hd : 1 ≤ d)
    (hrig : ∀ P : regularPolytopes d,
      ∃ i : Fin 3, regularSimilar d P (testimoneAlto d hd i)) :
    platonicCount d ≤ 3 := by
  classical
  have hsub : {S : Set (regularPolytopes d) |
      ∃ P, S = {Q : regularPolytopes d | regularSimilar d P Q}} ⊆
      Set.range (fun i : Fin 3 => classe d (testimoneAlto d hd i)) := by
    rintro S ⟨P, rfl⟩
    obtain ⟨i, hi⟩ := hrig P
    exact ⟨i, (classe_eq_of_similar_gen hi).symm⟩
  calc Set.encard {S : Set (regularPolytopes d) |
        ∃ P, S = {Q : regularPolytopes d | regularSimilar d P Q}}
      ≤ Set.encard
        (Set.range (fun i : Fin 3 => classe d (testimoneAlto d hd i))) :=
        Set.encard_le_encard hsub
    _ = Set.encard ((fun i : Fin 3 => classe d (testimoneAlto d hd i)) ''
        Set.univ) := by rw [Set.image_univ]
    _ ≤ Set.encard (Set.univ : Set (Fin 3)) := Set.encard_image_le _ _
    _ = 3 := by simp [Set.encard_univ]

/-- **L'EQUAZIONE FINALE CONDIZIONALE d≥5**: rigidità ⟹
`platonicCount d = 3`.  Combina il maggiorante con il minorante
incondizionato `three_le_platonicCount`.
@isnad1 id=eq.3h1v.s5.1a39186307f0 from=translated src=- shape=51937ea7 vocab=732a6632
-/
theorem platonicCount_eq_tre_di {d : ℕ} (hd1 : 1 ≤ d) (hd : 5 ≤ d)
    (hrig : ∀ P : regularPolytopes d,
      ∃ i : Fin 3, regularSimilar d P (testimoneAlto d hd1 i)) :
    platonicCount d = 3 :=
  le_antisymm (platonicCount_le_tre_di hd1 hrig) (three_le_platonicCount d hd)

end LeanEval.Geometry.PlatonicClassification
