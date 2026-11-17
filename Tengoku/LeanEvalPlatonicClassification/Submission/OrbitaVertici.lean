import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Generazione
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.ConnettivitaGlobale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, U4 — RIDUZIONE DELLA SURIETTIVITÀ ORBITALE (20 lug 2026).

Questo modulo chiude i due tratti non topologici di U4:

* ogni vertice di un politopo pieno in `E n`, per `n > 0`, è la faccia
  zero di una bandiera;
* una galleria dalla bandiera base a una bandiera radicata in `u` produce
  un elemento del sottogruppo semplice che manda il vertice base in `u`.

L'unica ipotesi lasciata esplicita nella suriettività finale è quindi la
connettività globale delle gallerie.  Nessun assioma geometrico viene
nascosto nella definizione dell'orbita.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccetta che contiene un vertice assegnato.  È la versione
radicata di `facet_exists`: l'invariante `v ∈ f` è preservato quando
`interpolazione` fa salire la faccia corrente.-/
theorem facet_exists_at_vertex (P : ConvexPolytope n) {d : ℕ}
    (hdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = d + 1)
    {v : E n} (hv : v ∈ P.vertices) :
    ∃ f : Set (E n), P.IsFace f ∧ faceDim f = d ∧ v ∈ f := by
  classical
  suffices H : ∀ k : ℕ, ∀ f : Set (E n), P.IsFace f → v ∈ f →
      d - faceDim f ≤ k → faceDim f ≤ d →
      ∃ g : Set (E n), P.IsFace g ∧ faceDim g = d ∧ v ∈ g by
    have hvface : P.IsFace ({v} : Set (E n)) := vertex_isFace P hv
    have hd0 : faceDim ({v} : Set (E n)) = 0 := faceDim_singleton v
    exact H d {v} hvface (Set.mem_singleton v)
      (by rw [hd0]; omega) (by rw [hd0]; omega)
  intro k
  induction k with
  | zero =>
      intro f hf hvf hk _hle
      exact ⟨f, hf, by omega, hvf⟩
  | succ m ih =>
      intro f hf hvf hk hle
      by_cases heq : faceDim f = d
      · exact ⟨f, hf, heq, hvf⟩
      · have hgap : faceDim f + 2 ≤
            Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
          rw [hdim]
          omega
        obtain ⟨f', hf', hff', hf'ne⟩ := interpolazione P hf hgap
        have hvf' : v ∈ f' := hff'.1 hvf
        have hlt : faceDim f < faceDim f' :=
          faceDim_lt_of_ssubset P hf hf' hff'
        have hf'top : f' ⊂ P.toSet := by
          refine ⟨face_subset_toSet P hf', ?_⟩
          intro htop
          exact hf'ne (Set.Subset.antisymm (face_subset_toSet P hf') htop)
        have hltTop : faceDim f' <
            Module.finrank ℝ (vectorSpan ℝ P.toSet) :=
          faceDim_lt_of_ssubset P hf' (toSet_isFace P) hf'top
        apply ih f' hf' hvf'
        · omega
        · rw [hdim] at hltTop
          omega

/-- Catena completa radicata in un vertice.  A differenza di
`chain_exists`, conserva esplicitamente `c 0 = {v}`.-/
theorem chain_exists_at_vertex (P : ConvexPolytope n) :
    ∀ d : ℕ, Module.finrank ℝ (vectorSpan ℝ P.toSet) = d →
    ∀ v : E n, v ∈ P.vertices →
    ∃ c : ℕ → Set (E n),
      c 0 = {v} ∧
      (∀ k, k < d → P.IsFace (c k) ∧ faceDim (c k) = k) ∧
      (∀ j k, j < k → k < d → c j ⊂ c k) := by
  classical
  intro d
  induction d generalizing P with
  | zero =>
      intro _ v _hv
      exact ⟨fun _ => {v}, rfl,
        fun k hk => absurd hk (by omega),
        fun j k hjk hk => absurd hk (by omega)⟩
  | succ m ih =>
      intro hdim v hv
      obtain ⟨f, hf, hfdim, hvf⟩ :=
        facet_exists_at_vertex P hdim hv
      let Q : ConvexPolytope n := facePolytope P hf
      have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = m := by
        dsimp only [Q]
        rw [facePolytope_toSet P hf]
        exact hfdim
      have hvQ : v ∈ Q.vertices := by
        change v ∈ P.vertices.filter (· ∈ f)
        exact Finset.mem_filter.mpr ⟨hv, hvf⟩
      obtain ⟨c', hc'0, hc'1, hc'2⟩ := ih Q hQdim v hvQ
      have hfzero : m = 0 → f = ({v} : Set (E n)) := by
        intro hm
        obtain ⟨x, hx⟩ := faccia_dim0_singoletto hf.2 (by simpa [hm] using hfdim)
        have hvx : v = x := by
          rw [hx] at hvf
          exact Set.mem_singleton_iff.mp hvf
        simpa [hvx] using hx
      refine ⟨fun k => if k = m then f else c' k, ?_, ?_, ?_⟩
      · change (if 0 = m then f else c' 0) = {v}
        by_cases hm : m = 0
        · rw [ite_eq_left hm.symm, hfzero hm]
        · rw [ite_eq_right (Ne.symm hm), hc'0]
      · intro k hk
        change P.IsFace (if k = m then f else c' k) ∧
          faceDim (if k = m then f else c' k) = k
        by_cases hkm : k = m
        · rw [ite_eq_left hkm]
          exact ⟨hf, hfdim.trans hkm.symm⟩
        · have hklt : k < m := by omega
          rw [ite_eq_right hkm]
          obtain ⟨hkface, hkdim⟩ := hc'1 k hklt
          exact ⟨isFace_of_facePolytope P hf hkface, hkdim⟩
      · intro j k hjk hk
        change (if j = m then f else c' j) ⊂
          (if k = m then f else c' k)
        by_cases hkm : k = m
        · have hjm : j ≠ m := by omega
          rw [ite_eq_left hkm, ite_eq_right hjm]
          obtain ⟨hjface, hjdim⟩ := hc'1 j (by omega)
          have hjsub : c' j ⊆ f := by
            have := face_subset_toSet Q hjface
            simpa only [Q, facePolytope_toSet P hf] using this
          refine hjsub.ssubset_of_ne ?_
          intro heq
          have := congrArg faceDim heq
          rw [hjdim, hfdim] at this
          omega
        · have hklt : k < m := by omega
          have hjm : j ≠ m := by omega
          simp only [ite_eq_right hkm, ite_eq_right hjm]
          exact hc'2 j k hjk hklt

/-- Ogni vertice di un politopo pieno di dimensione ambiente positiva
radica una bandiera, in dimensione arbitraria.-/
theorem bandiera_al_vertice_generica (P : ConvexPolytope n)
    (hfull : P.IsFullDim) (hn : 0 < n) {v : E n} (hv : v ∈ P.vertices) :
    ∃ F : P.Flag, F.face ⟨0, hn⟩ = {v} := by
  classical
  have hdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = n := hfull
  obtain ⟨c, hc0, hc1, hc2⟩ := chain_exists_at_vertex P n hdim v hv
  refine ⟨⟨fun k => c k, ?_, ?_, ?_⟩, ?_⟩
  · intro k
    exact (hc1 k k.isLt).1
  · intro k
    exact (hc1 k k.isLt).2
  · intro i j hij
    exact hc2 i j hij j.isLt
  · exact hc0

/-- L'orbita puntuale del vertice `v` sotto il sottogruppo semplice.
La forma esistenziale evita di introdurre una seconda istanza globale di
azione per le isometrie affini.-/
def simpleVertexOrbit (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (v : E n) : Set (E n) :=
  {u | ∃ w : symGroup P,
    w ∈ simpleSubgroup P hreg F ∧ (w : Isom n) v = u}

/-!
MANCANTE: `RidgeConnectedAboveOne P` senza ipotesi aggiuntive.

È precisamente la connettività del grafo delle faccette dentro ogni faccia
`B` di dimensione almeno 2.  Non è presente nel prior art con questa
generalità; richiede il teorema geometrico globale sulle faccette di un
politopo convesso arbitrario.  La vecchia `RidgeConnected P` non può essere
il kill-gate finale: quantifica anche su `faceDim B = 1` ed è falsa appena
esiste uno spigolo (`not_ridgeConnected_of_flag_two_le`).

La riduzione certificata è quindi:

`RidgeConnectedAboveOne P`
`→ ∀ F G, GalleryConnected P F G`
`→ P.vertices = simpleVertexOrbit P hreg F₀ v₀`.
-/

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
