import Tengoku.Erdos64.Erdos64.ComponentBoundaryCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two explicit components of the graph with `r` deleted determine the two
    root sides.  The component hypotheses are retained in the output so that
    the result is a decomposition certificate rather than a bare finset
    identity.
@isnad1 id=ex.12h5v.s8.4d6ac0013221 from=translated src=- shape=2d3acf0e vocab=eae9e510
-/
theorem twoRootDeletedComponents_partition
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (r : V) (C₁ C₂ : Finset V)
    (_hGconn : G.Connected)
    (hC₁nonempty : C₁.Nonempty)
    (hC₂nonempty : C₂.Nonempty)
    (hr₁ : r ∉ C₁)
    (hr₂ : r ∉ C₂)
    (hC₁conn : (G.induce (↑C₁ : Set V)).Connected)
    (hC₂conn : (G.induce (↑C₂ : Set V)).Connected)
    (hcross : ∀ x, x ∈ C₁ → ∀ y, y ∈ C₂ → ¬G.Adj x y)
    (hattach₁ : ∃ x, x ∈ C₁ ∧ G.Adj r x)
    (hattach₂ : ∃ x, x ∈ C₂ ∧ G.Adj r x)
    (hdisjoint : Disjoint C₁ C₂)
    (hcover : C₁ ∪ C₂ = Finset.univ.erase r) :
    ∃ A B : Finset V,
      A = {r} ∪ C₁ ∧
      B = {r} ∪ C₂ ∧
      C₁ ∪ C₂ = Finset.univ.erase r ∧
      Disjoint C₁ C₂ ∧
      A ∩ B = ({r} : Finset V) ∧
      A ∪ B = Finset.univ ∧
      A.Nonempty ∧ B.Nonempty ∧
      r ∈ A ∧ r ∈ B ∧
      C₁.Nonempty ∧ C₂.Nonempty ∧
      (G.induce (↑C₁ : Set V)).Connected ∧
      (G.induce (↑C₂ : Set V)).Connected ∧
      (∀ x, x ∈ C₁ → ∀ y, y ∈ C₂ → ¬G.Adj x y) ∧
      (∃ x, x ∈ C₁ ∧ G.Adj r x) ∧
      (∃ x, x ∈ C₂ ∧ G.Adj r x) := by
  have hinter :
      ({r} ∪ C₁ : Finset V) ∩ ({r} ∪ C₂ : Finset V) = {r} := by
    ext v
    by_cases hvr : v = r
    · simp [hvr]
    · constructor
      · intro hv
        rcases Finset.mem_inter.mp hv with ⟨hv₁, hv₂⟩
        rcases Finset.mem_union.mp hv₁ with hroot | h₁
        · exact (hvr (Finset.mem_singleton.mp hroot)).elim
        · rcases Finset.mem_union.mp hv₂ with hroot | h₂
          · exact (hr₁ (Finset.mem_singleton.mp hroot ▸ h₁)).elim
          · exact (Finset.disjoint_left.mp hdisjoint h₁ h₂).elim
      · intro hv
        exact (hvr (Finset.mem_singleton.mp hv)).elim
  have hunion :
      ({r} ∪ C₁ : Finset V) ∪ ({r} ∪ C₂ : Finset V) = Finset.univ := by
    ext v
    by_cases hvr : v = r
    · simp [hvr]
    · constructor
      · intro _
        exact Finset.mem_univ v
      · intro _
        have hverase : v ∈ Finset.univ.erase r := by
          simp [hvr]
        have hvc : v ∈ C₁ ∪ C₂ := by
          rw [← hcover] at hverase
          exact hverase
        rcases Finset.mem_union.mp hvc with hv₁ | hv₂
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr hv₁)))
        · exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inr hv₂)))
  refine ⟨{r} ∪ C₁, {r} ∪ C₂, rfl, rfl, hcover, hdisjoint,
    hinter, hunion, ?_, ?_, ?_, ?_, hC₁nonempty, hC₂nonempty,
    hC₁conn, hC₂conn, hcross, hattach₁, hattach₂⟩
  · exact ⟨r, by simp⟩
  · exact ⟨r, by simp⟩
  · simp
  · simp

end Erdos64
