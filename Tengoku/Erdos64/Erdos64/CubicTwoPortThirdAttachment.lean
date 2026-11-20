import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Three distinct boundary ports can be extracted from an explicit finite
boundary-neighbor set.  The carrier and boundary conditions are exposed
pointwise so this is a premise-producing lemma rather than a forcing claim.-/
theorem exists_three_distinct_boundary_attachments
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K B : Finset V)
    (hB : ∀ w, w ∈ B ↔ w ∉ K ∧ ∃ x, x ∈ K ∧ G.Adj x w)
    (hBcard : 3 ≤ B.card) :
    ∃ a b c : V,
      a ∈ B ∧ b ∈ B ∧ c ∈ B ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∉ K ∧ b ∉ K ∧ c ∉ K ∧
      (∃ x, x ∈ K ∧ G.Adj x a) ∧
      (∃ x, x ∈ K ∧ G.Adj x b) ∧
      (∃ x, x ∈ K ∧ G.Adj x c) := by
  classical
  have hBpos : 0 < B.card := by omega
  obtain ⟨a, haB⟩ := Finset.card_pos.mp hBpos
  have hBera : 2 ≤ (B.erase a).card := by
    rw [Finset.card_erase_of_mem haB]
    omega
  obtain ⟨b, hbErase⟩ := Finset.card_pos.mp (show 0 < (B.erase a).card by omega)
  have hab : a ≠ b := (Finset.mem_erase.mp hbErase).1.symm
  have hbB : b ∈ B := (Finset.mem_erase.mp hbErase).2
  have hCpos : 0 < ((B.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hbErase]
    omega
  obtain ⟨c, hcErase⟩ := Finset.card_pos.mp hCpos
  have hbc : b ≠ c := (Finset.mem_erase.mp hcErase).1.symm
  have hcEraseA : c ∈ B.erase a := (Finset.mem_erase.mp hcErase).2
  have hac : a ≠ c := (Finset.mem_erase.mp hcEraseA).1.symm
  have hcB : c ∈ B := (Finset.mem_erase.mp hcEraseA).2
  have haData := (hB a).mp haB
  have hbData := (hB b).mp hbB
  have hcData := (hB c).mp hcB
  exact ⟨a, b, c, haB, hbB, hcB, hab, hac, hbc,
    haData.1, hbData.1, hcData.1, haData.2, hbData.2, hcData.2⟩

end Erdos64
