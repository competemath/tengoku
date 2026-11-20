import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

open PentagramEarHull

universe u

variable {V : Type u} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem two_le_internalDegree_of_neighbors
    (S : Finset V) (v a b : V) (hab : a ≠ b)
    (ha : a ∈ S) (hb : b ∈ S)
    (hva : G.Adj v a) (hvb : G.Adj v b) :
    2 ≤ internalDegree G S v := by
  have hsub : ({a, b} : Finset V) ⊆ S.filter (G.Adj v) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, hva⟩
    · exact Finset.mem_filter.mpr ⟨hb, hvb⟩
  simpa [internalDegree, hab] using Finset.card_le_card hsub

private theorem three_le_internalDegree_of_neighbors
    (S : Finset V) (v a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c) :
    3 ≤ internalDegree G S v := by
  have hsub : ({a, b, c} : Finset V) ⊆ S.filter (G.Adj v) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, hva⟩
    · exact Finset.mem_filter.mpr ⟨hb, hvb⟩
    · exact Finset.mem_filter.mpr ⟨hc, hvc⟩
  simpa [internalDegree, hab, hac, hbc] using Finset.card_le_card hsub

/-- Every nonempty exterior carrier closed except into the hull has a private
`b` attachment: precisely its two prescribed neighbors remain after deletion.-/
theorem private_b_of_closed_exterior
    (H : PentagramEarHull G)
    (hmin : 3 ≤ G.minDegree)
    (hcrit : IsSubgraphCritical G)
    (D : Finset V) (hD : D.Nonempty)
    (hext : ∀ v, v ∈ D → v ∉ H.hull)
    (hclosed : ∀ x, x ∈ D → ∀ y,
      G.Adj x y → y ∈ D ∨ y ∈ H.hull) :
    ∃ i : Fin 5,
      internalDegree G (Finset.univ \ D) (H.bVertex i) = 2 ∧
      (∀ w, G.Adj (H.bVertex i) w →
        w = H.aVertex i ∨ w = H.aVertex (i + 2) ∨ w ∈ D) ∧
      (∃ w, w ∈ D ∧ G.Adj (H.bVertex i) w) := by
  classical
  let U : Finset V := Finset.univ.filter (fun v => v ∈ H.hull)
  have hU_iff (v : V) : v ∈ U ↔ v ∈ H.hull := by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc_mem (i : Fin 5) : H.cVertex i ∈ U :=
    (hU_iff _).mpr (Or.inl (Or.inl ⟨i, rfl⟩))
  have ha_mem (i : Fin 5) : H.aVertex i ∈ U :=
    (hU_iff _).mpr (Or.inl (Or.inr ⟨i, rfl⟩))
  have hb_mem (i : Fin 5) : H.bVertex i ∈ U :=
    (hU_iff _).mpr (Or.inr ⟨i, rfl⟩)
  have hca_ne (i j : Fin 5) : H.cVertex i ≠ H.aVertex j := by
    intro h
    have he := H.vertex_injective h
    cases he
  have hcb_ne (i j : Fin 5) : H.cVertex i ≠ H.bVertex j := by
    intro h
    have he := H.vertex_injective h
    cases he
  have haa_ne (i : Fin 5) : H.aVertex i ≠ H.aVertex (i + 2) := by
    intro h
    have he := H.aVertex_injective h
    have hn : i ≠ i + 2 := by fin_cases i <;> decide
    exact hn he
  have hc_degree (i : Fin 5) : 3 ≤ internalDegree G U (H.cVertex i) := by
    have hnext : i + 4 + 1 = i := by fin_cases i <;> decide
    have hprev : G.Adj (H.cVertex i) (H.cVertex (i + 4)) := by
      simpa only [PentagramEarHull.cVertex, hnext] using
        G.adj_symm (H.c_adj (i + 4))
    have hcc : H.cVertex (i + 1) ≠ H.cVertex (i + 4) := by
      intro h
      have he := H.cVertex_injective h
      have hn : i + 1 ≠ i + 4 := by fin_cases i <;> decide
      exact hn he
    exact three_le_internalDegree_of_neighbors U (H.cVertex i)
      (H.cVertex (i + 1)) (H.cVertex (i + 4)) (H.aVertex i)
      hcc (hca_ne _ _) (hca_ne _ _)
      (hc_mem _) (hc_mem _) (ha_mem _) (H.c_adj i) hprev (H.ca_adj i)
  have ha_degree (i : Fin 5) : 3 ≤ internalDegree G U (H.aVertex i) := by
    have hnext : i + 3 + 2 = i := by fin_cases i <;> decide
    have hshift : G.Adj (H.aVertex i) (H.bVertex (i + 3)) := by
      simpa only [PentagramEarHull.aVertex, PentagramEarHull.bVertex, hnext] using
        H.shifted_ab_adj (i + 3)
    have hbb : H.bVertex i ≠ H.bVertex (i + 3) := by
      intro h
      have he := H.bVertex_injective h
      have hn : i ≠ i + 3 := by fin_cases i <;> decide
      exact hn he
    exact three_le_internalDegree_of_neighbors U (H.aVertex i)
      (H.cVertex i) (H.bVertex i) (H.bVertex (i + 3))
      (hcb_ne _ _) (hcb_ne _ _) hbb
      (hc_mem _) (hb_mem _) (hb_mem _)
      (G.adj_symm (H.ca_adj i)) (H.ab_adj i) hshift
  have hb_degree (i : Fin 5) : 2 ≤ internalDegree G U (H.bVertex i) :=
    two_le_internalDegree_of_neighbors U (H.bVertex i)
      (H.aVertex i) (H.aVertex (i + 2)) (haa_ne i)
      (ha_mem _) (ha_mem _) (G.adj_symm (H.ab_adj i))
      (G.adj_symm (H.shifted_ab_adj i))
  have hU_degree : ∀ v, v ∈ U → 2 ≤ internalDegree G U v := by
    intro v hv
    rcases (hU_iff v).mp hv with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
    · exact le_trans (by decide : 2 ≤ 3) (hc_degree i)
    · exact le_trans (by decide : 2 ≤ 3) (ha_degree i)
    · exact hb_degree i
  have hmin_finset : ∀ v, 3 ≤ (Finset.univ.filter (G.Adj v)).card := by
    intro v
    have heq : Finset.univ.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
    rw [heq, SimpleGraph.card_neighborFinset_eq_degree]
    exact degree_ge_three_of_minDegree_ge_three G hmin v
  have hdisjoint : Disjoint U D := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvD
    exact hext v hvD ((hU_iff v).mp hvU)
  have hseparated : ∀ x, x ∉ U → x ∉ D →
      ∀ y, y ∈ D → ¬G.Adj x y := by
    intro x hxU hxD y hyD hxy
    rcases hclosed y hyD x (G.adj_symm hxy) with hx | hx
    · exact hxD hx
    · exact hxU ((hU_iff x).mpr hx)
  obtain ⟨v, hvU, _, hvlow, hvD⟩ :=
    exists_deficient_boundary_vertex G hmin_finset hcrit
      ⟨H.cVertex 0, hc_mem 0⟩ hD hdisjoint hU_degree hseparated
  have hUS : U ⊆ Finset.univ \ D := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w,
      fun hwD => hext w hwD ((hU_iff w).mp hw)⟩
  have hmono (w : V) : internalDegree G U w ≤
      internalDegree G (Finset.univ \ D) w := by
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_filter.mpr
      ⟨hUS (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
  rcases (hU_iff v).mp hvU with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · have hthree := le_trans (hc_degree i) (hmono (H.cVertex i))
    omega
  · have hthree := le_trans (ha_degree i) (hmono (H.aVertex i))
    omega
  · have htwo := le_trans (hb_degree i) (hmono (H.bVertex i))
    refine ⟨i, le_antisymm hvlow htwo, ?_, hvD⟩
    intro w hw
    by_cases hwa : w = H.aVertex i
    · exact Or.inl hwa
    by_cases hwb : w = H.aVertex (i + 2)
    · exact Or.inr (Or.inl hwb)
    apply Or.inr
    apply Or.inr
    by_contra hwD
    have hthree := three_le_internalDegree_of_neighbors (Finset.univ \ D)
      (H.bVertex i) (H.aVertex i) (H.aVertex (i + 2)) w
      (haa_ne i) (Ne.symm hwa) (Ne.symm hwb)
      (hUS (ha_mem i)) (hUS (ha_mem (i + 2)))
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwD⟩)
      (G.adj_symm (H.ab_adj i)) (G.adj_symm (H.shifted_ab_adj i)) hw
    omega

end Erdos64
