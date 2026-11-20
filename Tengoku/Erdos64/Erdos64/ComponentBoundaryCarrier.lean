import Tengoku.Erdos64.Erdos64.LeafBlockArticulationDefect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A finite cut decomposition supplies a genuine leaf-block carrier.  The
    component side `K` and the complementary side `R` partition the vertices,
    while all non-root cross-edges are excluded.  The output is the enlarged
    side `{r} ∪ K`, with its exact one-root boundary and nonroot closure
    exposed for downstream criticality arguments.-/
theorem cutComponent_to_leafBlockCarrier
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K R : Finset V) (r : V)
    (hKnonempty : K.Nonempty)
    (hrR : r ∈ R)
    (hpartition : K ∪ R = (Finset.univ : Finset V))
    (hdisjoint : Disjoint K R)
    (hRother : ∃ z, z ∈ R ∧ z ≠ r)
    (hblockconn :
      (G.induce (↑({r} ∪ K) : Set V)).Connected)
    (hnoncross :
      ∀ x, x ∈ K → ∀ y, y ∈ R → y ≠ r → ¬G.Adj x y) :
    ∃ S : Finset V,
      S = {r} ∪ K ∧
      S.Nonempty ∧
      S ≠ (Finset.univ : Finset V) ∧
      r ∈ S ∧
      (∃ x, x ∈ S ∧ x ≠ r) ∧
      (G.induce (↑S : Set V)).Connected ∧
      (∀ x, x ∈ S → ∀ y, y ∉ S → G.Adj x y → x = r) ∧
      (∀ x, x ∈ S → x ≠ r → ∀ y, G.Adj x y → y ∈ S) := by
  have hboundary :
      ∀ x, x ∈ ({r} ∪ K : Finset V) →
        ∀ y, y ∉ ({r} ∪ K : Finset V) → G.Adj x y → x = r := by
    intro x hxS y hyS hxy
    rcases Finset.mem_union.mp hxS with hxr | hxK
    · exact Finset.mem_singleton.mp hxr
    · have hyR : y ∈ R := by
        have hyU : y ∈ K ∪ R := by
          rw [hpartition]
          exact Finset.mem_univ y
        rcases Finset.mem_union.mp hyU with hyK | hyR
        · exact (hyS (Finset.mem_union.mpr (Or.inr hyK))).elim
        · exact hyR
      have hyr : y ≠ r := by
        intro hyr
        subst y
        exact hyS (Finset.mem_union.mpr
          (Or.inl (Finset.mem_singleton.mpr rfl)))
      exact (hnoncross x hxK y hyR hyr hxy).elim
  have hclosure :
      ∀ x, x ∈ ({r} ∪ K : Finset V) → x ≠ r →
        ∀ y, G.Adj x y → y ∈ ({r} ∪ K : Finset V) := by
    intro x hxS hxr y hxy
    by_contra hyS
    exact hxr (hboundary x hxS y hyS hxy)
  refine ⟨{r} ∪ K, rfl, ?_, ?_, ?_, ?_, hblockconn, hboundary, hclosure⟩
  · exact ⟨r, by simp⟩
  · obtain ⟨z, hzR, hzr⟩ := hRother
    intro hS
    have hzS : z ∈ ({r} ∪ K : Finset V) := by
      rw [hS]
      exact Finset.mem_univ z
    rcases Finset.mem_union.mp hzS with hzroot | hzK
    · exact hzr (Finset.mem_singleton.mp hzroot)
    · exact (Finset.disjoint_left.mp hdisjoint hzK hzR)
  · simp
  · obtain ⟨x, hxK⟩ := hKnonempty
    refine ⟨x, Finset.mem_union.mpr (Or.inr hxK), ?_⟩
    intro hxr
    exact (Finset.disjoint_left.mp hdisjoint hxK (hxr ▸ hrR)).elim

end Erdos64
