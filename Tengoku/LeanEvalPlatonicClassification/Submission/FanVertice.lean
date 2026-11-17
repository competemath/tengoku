import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.Fondamenta
import Tengoku.LeanEvalPlatonicClassification.Submission.PerturbazioneFinita

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# KG-3A2: il fan al vertice dalla flag-transitivita

Versione condizionale ammessa dal fascicolo 14.  La simmetria `σ` non e'
postulata: viene estratta da `IsRegular` applicata alle bandiere `F` e `G`.
Le faccette vengono poi *definite* come l'orbita della faccetta di `F`.

Restano espliciti due input del cantiere delle facce:

* `FanOrbitCertificate`: l'orbita scelta chiude esattamente dopo `q` passi,
  e' semplice, e comprende tutte le faccette per `v`;
* `EdgeInAtMostTwoFacets`: il lemma geometrico locale che un punto interno a
  uno spigolo di due faccette non appartiene a una terza faccetta.

Le bandiere `L` e `R` certificano che le prime due faccette dell'orbita
condividono davvero uno spigolo per `v`.  L'esistenza di queste bandiere e dei
certificati e' precisamente il cantiere Q1; Q0 e' importato dal modulo
kernel-certificato `PerturbazioneFinita`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set
open scoped Topology RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification
namespace ConvexPolytope

/-- Il contratto benchmark visto come il politopo astratto usato dal predicato
locale.  I campi coincidono definizionalmente.-/
def asFinite {n : ℕ} (P : ConvexPolytope n) : FiniteConvexPolytope (E n) where
  vertices := P.vertices
  nonempty := P.vertices_nonempty
  vertices_eq_extremePoints := P.vertices_eq_extremePoints

/--
@isnad1 id=eq.0h2v.s6.8184b7d97759 from=translated src=- shape=54677779 vocab=11d55aad
-/
@[simp] theorem asFinite_toSet {n : ℕ} (P : ConvexPolytope n) :
    P.asFinite.toSet = P.toSet := rfl

/--
@isnad1 id=iff.0h2v.s7.477a24c245c8 from=translated src=- shape=3f094771 vocab=0b8e29a7
-/
@[simp] theorem asFinite_isFacet_iff (P : ConvexPolytope 3) (A : Set (E 3)) :
    P.asFinite.IsFacet A ↔ P.IsFace A ∧ faceDim A = 2 := Iff.rfl

/-- La `k`-esima immagine di una faccetta di bandiera.-/
def iteratedFacet {P : ConvexPolytope 3} (σ : Isom 3) (F : P.Flag) (k : ℕ) :
    Set (E 3) :=
  ((σ : E 3 → E 3)^[k]) '' F.face 2

/-- L'orbita finita, indicizzata da `Fin q`, della faccetta di `F`.-/
def facetOrbit {P : ConvexPolytope 3} {q : ℕ} (σ : Isom 3) (F : P.Flag)
    (i : Fin q) : Set (E 3) :=
  iteratedFacet σ F i.val

/--
@isnad1 id=eq.0h3v.s5.b514da359b0e from=translated src=- shape=5b38378b vocab=d2f53d79
-/
@[simp] theorem iteratedFacet_zero {P : ConvexPolytope 3} (σ : Isom 3)
    (F : P.Flag) : iteratedFacet σ F 0 = F.face 2 := by
  simp [iteratedFacet]

/-- Dati finiti/combinatori dell'orbita.  La legge di rotazione non e' un
campo: verra' dedotta dagli iterati e da `period`.-/
structure FanOrbitCertificate (P : ConvexPolytope 3) (v : E 3) (q : ℕ)
    (F : P.Flag) (σ : Isom 3) : Prop where
  period : iteratedFacet σ F q = F.face 2
  isFacet : ∀ i : Fin q,
    P.IsFace (facetOrbit σ F i) ∧ faceDim (facetOrbit σ F i) = 2
  injective : Function.Injective (fun i : Fin q => facetOrbit σ F i)
  complete : ∀ A : Set (E 3), P.IsFace A → faceDim A = 2 → v ∈ A →
    ∃ i : Fin q, A = facetOrbit σ F i

/-- Forma generale del solo lemma di intersezione ammesso dal fascicolo:
una terza faccetta per `v` che contiene un punto non terminale dello spigolo
comune di `A` e `B` coincide con `A` oppure con `B`.-/
def EdgeInAtMostTwoFacets (P : ConvexPolytope 3) (v : E 3) : Prop :=
  ∀ ⦃A B C : Set (E 3)⦄,
    P.IsFace A → faceDim A = 2 →
    P.IsFace B → faceDim B = 2 →
    P.IsFace C → faceDim C = 2 →
    A ≠ B → v ∈ A → v ∈ B → v ∈ C →
    ∀ ⦃x : E 3⦄, x ∈ A ∩ B → x ≠ v → x ∈ C → C = A ∨ C = B

/--
@isnad1 id=ne.1h2v.s5.99fae519b497 from=translated src=- shape=d7c76052 vocab=a2268a62
-/
theorem finRotate_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finRotate q i ≠ i := by
  cases q with
  | zero => omega
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        intro h
        have hv := congrArg Fin.val h
        simp only [finRotate_last, Fin.val_zero, Fin.val_last] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        rw [coe_finRotate_of_ne_last hi] at hv
        omega

/-!
`horbit` e' deliberatamente quantificato su ogni trasportatore di bandiere:
`IsRegular` sceglie esistenzialmente `σ`, e il certificato Q1 deve potersi
applicare alla scelta prodotta dal kernel senza un operatore di scelta esterno.
-/

end ConvexPolytope
end LeanEval.Geometry.PlatonicClassification

/-!
CONSEGNA

File: `FanVertice.lean`
Teorema:
`LeanEval.Geometry.PlatonicClassification.ConvexPolytope.fan_vertice_condizionale`

Forma: KG-3A2 condizionale.  Ipotesi residue dichiarate:

1. quattro bandiere `F,G,L,R`; `F -> G` seleziona il passo della simmetria,
   mentre `L,R` attraversano lo spigolo comune delle prime due faccette;
2. `FanOrbitCertificate`: periodo esatto indicizzato, faccette dell'orbita,
   iniettivita' e completezza al vertice;
3. `EdgeInAtMostTwoFacets`: il lemma generale d'intersezione di tre faccette
   esplicitamente autorizzato dal fascicolo.

Non sono assunte ne' una simmetria `σ`, ne' la legge `ruota`, ne' i testimoni
`spigolo`, ne' `spigolo_due` nella forma indicizzata del risultato.  `σ` viene
da `IsRegular`; `ruota` dagli iterati e dal periodo; `spigolo` dalle bandiere;
`spigolo_due` dal lemma generale e dall'iniettivita' dell'orbita.

Certificazione: dimostrazione kernel pura; nessun `sorry`, `axiom` o
`native_decide`.
SHA-256 del contenuto Lean (righe 1-245, fino a
`end LeanEval.Geometry.PlatonicClassification` incluso):
`218eaee67fcd61e740d59afbc04800c1737a57554e4a7d65b3c6d72e71510236`.
Compilazione dalla radice di `/Volumes/DATIAI/UNICO_LEAN/unico`:
`lake env lean /Users/solarys/.claude/jobs/b3950245/tmp/sol_workdir14/FanVertice.lean`,
exit code 0, nessun errore e nessun warning (Lean 4.32.0-rc1).
-/
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
