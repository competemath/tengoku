import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.VerticiEsposti
import Tengoku.LeanEvalPlatonicClassification.Submission.SottoPolitopo
import Tengoku.LeanEvalPlatonicClassification.Submission.DimStretta
import Tengoku.LeanEvalPlatonicClassification.Submission.Interpolazione
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraCompagna
import Tengoku.LeanEvalPlatonicClassification.Submission.Diamante
import Tengoku.LeanEvalPlatonicClassification.Submission.Diamante2D
import Tengoku.LeanEvalPlatonicClassification.Submission.SecondoSpigolo
import Tengoku.LeanEvalPlatonicClassification.Submission.ConoVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.Camminata

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FASE 3A, F9a — LA CONNETTIVITÀ DEL POLIGONO (18 lug 2026).

In un poligono (politopo di rango 2) il grafo dei vertici con gli spigoli
come lati è connesso: la camminata del simplesso con il potenziale dato
dall'espositore del vertice bersaglio. Il principio locale-globale è il
cono al vertice (ConoVertice); i vicini di un vertice sono gli altri
estremi dei suoi (esattamente due) spigoli; il massimo del potenziale è
unico per la caratterizzazione argmax del vertice esposto.

Prima un attrezzo: un vertice del politopo dentro uno spigolo-segmento ne
è un estremo (parametrizzazione + estremalità).
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Un vertice del politopo dentro un segmento ne è un estremo.
@isnad1 id=or.5h6v.s7.64cc065923d6 from=translated src=- shape=1f1c666b vocab=a9e50259
-/
theorem vertice_estremo_del_segmento (P : ConvexPolytope n)
    {e : Set (E n)} (he : P.IsFace e)
    {a b : E n} (hseg : e = segment ℝ a b) (hab : a ≠ b)
    {x : E n} (hxV : x ∈ P.vertices) (hxe : x ∈ e) :
    x = a ∨ x = b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hex : x ∈ e.extremePoints ℝ := vertice_estremo_in_faccia P he hxV hxe
  have hxseg : x ∈ segment ℝ a b := by
    rw [← hseg]
    exact hxe
  obtain ⟨s, t, hs, ht, hst, hx⟩ := hxseg
  have hae : a ∈ e := by
    rw [hseg]
    exact left_mem_segment ℝ a b
  have hbe : b ∈ e := by
    rw [hseg]
    exact right_mem_segment ℝ a b
  -- s e t sono entrambi positivi, altrimenti x sarebbe un estremo
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hs with h | h
    · exact h
    · exfalso
      apply hcon.2
      have ht1 : t = 1 := by
        rw [← h] at hst
        simpa using hst
      rw [← hx, ← h, ht1]
      simp
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      apply hcon.1
      have hs1 : s = 1 := by
        rw [← h] at hst
        simpa using hst
      rw [← hx, ← h, hs1]
      simp
  have hopen : x ∈ openSegment ℝ a b := ⟨s, t, hspos, htpos, hst, hx⟩
  have h2 := hex.2 hae hbe hopen
  exact hcon.1 h2.symm

end LeanEval.Geometry.PlatonicClassification
