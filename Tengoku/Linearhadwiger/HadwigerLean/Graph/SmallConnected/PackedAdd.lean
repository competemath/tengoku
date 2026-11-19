import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedCount
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending a connected block family by a disjoint connected block
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

/--
@isnad1 id=le.1h4v.s5.9d98530270a7 from=translated src=- shape=0ffda8cb vocab=3df54915
-/
theorem ConnectedBlockFamily.block_subset_covered
    (B : Finset V) (hB : B ∈ F.blocks) : B ⊆ F.covered := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨B, hB, hv⟩

/--
@isnad1 id=not.2h4v.s5.8d825fbdb12e from=translated src=- shape=2e6094d9 vocab=4634bad1
-/
theorem ConnectedBlockFamily.not_mem_blocks_of_disjoint_covered
    (H : Finset V) (hH : H.Nonempty)
    (hdisj : Disjoint H F.covered) : H ∉ F.blocks := by
  intro hHF
  obtain ⟨v, hv⟩ := hH
  exact (Finset.disjoint_left.mp hdisj hv)
    (F.block_subset_covered H hHF hv)

/-- Append one connected block disjoint from the currently covered set.-/
noncomputable def ConnectedBlockFamily.add
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) : ConnectedBlockFamily G where
  blocks := insert H F.blocks
  connected := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hBF
    · exact hconn
    · exact F.connected B hBF
  disjoint := by
    intro B hB C hC hBC
    rcases Finset.mem_insert.mp hB with rfl | hBF
    · rcases Finset.mem_insert.mp hC with rfl | hCF
      · exact False.elim (hBC rfl)
      · apply Set.disjoint_left.mpr
        intro v hvH hvC
        exact (Finset.disjoint_left.mp hdisj hvH)
          (F.block_subset_covered C hCF hvC)
    · rcases Finset.mem_insert.mp hC with rfl | hCF
      · apply Set.disjoint_left.mpr
        intro v hvB hvH
        exact (Finset.disjoint_left.mp hdisj hvH)
          (F.block_subset_covered B hBF hvB)
      · exact F.disjoint B hBF C hCF hBC

/--
@isnad1 id=eq.2h4v.s6.53f0e982a6b0 from=translated src=- shape=a82230f1 vocab=d2512918
-/
theorem ConnectedBlockFamily.covered_add
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    (F.add H hconn hdisj).covered = H ∪ F.covered := by
  simp [ConnectedBlockFamily.add, ConnectedBlockFamily.covered]

/--
@isnad1 id=eq.2h4v.s6.60c9d3200c72 from=translated src=- shape=ff5207e6 vocab=7f5ca945
-/
theorem ConnectedBlockFamily.blocks_card_add
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    (F.add H hconn hdisj).blocks.card = F.blocks.card + 1 := by
  have hH : H.Nonempty := by
    obtain ⟨v⟩ := hconn.nonempty
    exact ⟨v.1, v.2⟩
  have hnot : H ∉ F.blocks :=
    F.not_mem_blocks_of_disjoint_covered H hH hdisj
  simp [ConnectedBlockFamily.add, hnot, Nat.add_comm]

end HadwigerLean
