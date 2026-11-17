import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.ConteggioBenchmark

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
IL MINORANTE CONDIZIONALE IN DIMENSIONE QUATTRO.

Se esistono sei politopi regolari quadridimensionali con rispettivamente
`5`, `8`, `16`, `24`, `120` e `600` vertici, le loro classi di similitudine
sono distinte.  Sono quindi sei elementi distinti dell'insieme contato da
`platonicCount 4`.
-/

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

theorem sei_le_platonicCount_quattro_di
    (P₁ P₂ P₃ P₄ P₅ P₆ : ConvexPolytope 4)
    (h₁ : P₁.IsRegular) (h₂ : P₂.IsRegular) (h₃ : P₃.IsRegular)
    (h₄ : P₄.IsRegular) (h₅ : P₅.IsRegular) (h₆ : P₆.IsRegular)
    (hc₁ : P₁.vertices.card = 5) (hc₂ : P₂.vertices.card = 8)
    (hc₃ : P₃.vertices.card = 16) (hc₄ : P₄.vertices.card = 24)
    (hc₅ : P₅.vertices.card = 120) (hc₆ : P₆.vertices.card = 600) :
    6 ≤ platonicCount 4 := by
  classical
  set e1 : regularPolytopes 4 := ⟨P₁, h₁⟩ with he1
  set e2 : regularPolytopes 4 := ⟨P₂, h₂⟩ with he2
  set e3 : regularPolytopes 4 := ⟨P₃, h₃⟩ with he3
  set e4 : regularPolytopes 4 := ⟨P₄, h₄⟩ with he4
  set e5 : regularPolytopes 4 := ⟨P₅, h₅⟩ with he5
  set e6 : regularPolytopes 4 := ⟨P₆, h₆⟩ with he6
  have h12 : classe 4 e1 ≠ classe 4 e2 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₂.vertices.card = P₁.vertices.card at hv
    omega
  have h13 : classe 4 e1 ≠ classe 4 e3 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₃.vertices.card = P₁.vertices.card at hv
    omega
  have h14 : classe 4 e1 ≠ classe 4 e4 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₄.vertices.card = P₁.vertices.card at hv
    omega
  have h15 : classe 4 e1 ≠ classe 4 e5 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₅.vertices.card = P₁.vertices.card at hv
    omega
  have h16 : classe 4 e1 ≠ classe 4 e6 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₆.vertices.card = P₁.vertices.card at hv
    omega
  have h23 : classe 4 e2 ≠ classe 4 e3 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₃.vertices.card = P₂.vertices.card at hv
    omega
  have h24 : classe 4 e2 ≠ classe 4 e4 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₄.vertices.card = P₂.vertices.card at hv
    omega
  have h25 : classe 4 e2 ≠ classe 4 e5 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₅.vertices.card = P₂.vertices.card at hv
    omega
  have h26 : classe 4 e2 ≠ classe 4 e6 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₆.vertices.card = P₂.vertices.card at hv
    omega
  have h34 : classe 4 e3 ≠ classe 4 e4 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₄.vertices.card = P₃.vertices.card at hv
    omega
  have h35 : classe 4 e3 ≠ classe 4 e5 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₅.vertices.card = P₃.vertices.card at hv
    omega
  have h36 : classe 4 e3 ≠ classe 4 e6 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₆.vertices.card = P₃.vertices.card at hv
    omega
  have h45 : classe 4 e4 ≠ classe 4 e5 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₅.vertices.card = P₄.vertices.card at hv
    omega
  have h46 : classe 4 e4 ≠ classe 4 e6 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₆.vertices.card = P₄.vertices.card at hv
    omega
  have h56 : classe 4 e5 ≠ classe 4 e6 := by
    intro h
    have hv := vertices_card_of_similar (similar_of_classe_eq h)
    change P₆.vertices.card = P₅.vertices.card at hv
    omega
  have hsub :
      ({classe 4 e1, classe 4 e2, classe 4 e3, classe 4 e4, classe 4 e5,
          classe 4 e6} : Set (Set (regularPolytopes 4)))
        ⊆ {S | ∃ P', S = {Q : regularPolytopes 4 | regularSimilar 4 P' Q}} := by
    intro S hS
    rcases hS with h | h | h | h | h | h <;> subst h <;>
      first
        | exact classe_mem_quoziente 4 e1
        | exact classe_mem_quoziente 4 e2
        | exact classe_mem_quoziente 4 e3
        | exact classe_mem_quoziente 4 e4
        | exact classe_mem_quoziente 4 e5
        | exact classe_mem_quoziente 4 e6
  have hcard :
      ({classe 4 e1, classe 4 e2, classe 4 e3, classe 4 e4, classe 4 e5,
          classe 4 e6} : Set (Set (regularPolytopes 4))).encard = 6 := by
    rw [Set.encard_insert_of_notMem (by simp [h12, h13, h14, h15, h16]),
      Set.encard_insert_of_notMem (by simp [h23, h24, h25, h26]),
      Set.encard_insert_of_notMem (by simp [h34, h35, h36]),
      Set.encard_insert_of_notMem (by simp [h45, h46]),
      Set.encard_insert_of_notMem (by simp [h56]),
      Set.encard_singleton]
    rfl
  change (6 : ℕ∞) ≤ Set.encard _
  calc
    (6 : ℕ∞) = _ := hcard.symm
    _ ≤ _ := Set.encard_le_encard hsub

end LeanEval.Geometry.PlatonicClassification
