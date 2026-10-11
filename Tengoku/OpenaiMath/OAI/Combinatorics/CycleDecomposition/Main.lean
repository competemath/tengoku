import Tengoku.OpenaiMath.OAI.Combinatorics.CycleDecomposition.LayerCosts

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

def Layers.pieceSequence (H : Layers P Dstar) (j : ℕ) : ℝ :=
  if j < H.count then H.pieceMass j else 0

lemma Layers.pieceSequence_nonneg (H : Layers P Dstar) (j) : 0 ≤ H.pieceSequence j := by
  unfold Layers.pieceSequence
  split_ifs
  · exact vertexMass_nonneg _
  · rfl

lemma Layers.pieceSequence_zero (H : Layers P Dstar) (j) (hj : H.count ≤ j) :
    H.pieceSequence j = 0 := by simp only [Layers.pieceSequence,ite_eq_right (by omega : ¬ j < H.count)]

lemma Layers.past_mass_eq_sequence (H : Layers P Dstar) (k) (hk : k ≤ H.count) :
    vertexMass (pastPieces H.system 0 k [P]) = ∑ j ∈ range k, H.pieceSequence j := by
  rw [pastPieces_mass]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.zero_add,Layers.pieceSequence,ite_eq_left (by have := Finset.mem_range.mp hj; omega : j < H.count)]

lemma Layers.prefix_choice (H : Layers P Dstar) :
    vertexMass (pastPieces H.system 0 H.count [P]) = 0 ∨
    ∃ i < H.count, 0 < H.pieceMass i ∧
      ∀ k ≤ H.count, k ≤ i+201 →
        vertexMass (pastPieces H.system 0 k [P]) ≤ ErdosGallai.mainP*H.pieceMass i := by
  by_cases he : ∃ j, 0 < H.pieceSequence j
  · right
    obtain ⟨i,hi,hpref⟩ := ErdosGallai.prefix_selection H.pieceSequence H.pieceSequence_nonneg
      200 H.count H.pieceSequence_zero he
    have hic : i < H.count := by
      by_contra hi'
      rw [H.pieceSequence_zero i (by omega)] at hi
      linarith
    simp only [Layers.pieceSequence,ite_eq_left hic] at hi
    refine ⟨i,hic,hi,?_⟩
    intro k hk hki
    rw [H.past_mass_eq_sequence k hk]
    have hh : (∑ j ∈ range k, H.pieceSequence j) ≤ ∑ j ∈ range (i+200+1), H.pieceSequence j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => H.pieceSequence_nonneg j)
    apply hh.trans
    norm_num only [Layers.pieceSequence,ite_eq_left hic,ErdosGallai.mainP,Nat.cast_ofNat] at hpref ⊢
    exact hpref
  · left
    rw [H.past_mass_eq_sequence H.count le_rfl]
    apply Finset.sum_eq_zero
    intro j _
    exact le_antisymm (le_of_not_gt (fun h => he ⟨j,h⟩)) (H.pieceSequence_nonneg j)

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

lemma main_edge_bound {V : Type} [Fintype V] (G : SimpleGraph V) :
    2*(Scale.edgeCount G:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
  classical
  have h : (G.edgeFinset.card:ℝ) ≤ ((Fintype.card V).choose 2:ℝ) :=
    Nat.cast_le.mpr G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at h
  change 2*(G.edgeFinset.card:ℝ) ≤ _
  nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)]

lemma main_cost_eq_scale {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Scale.decompositionCost G := by rfl
lemma main_cost_eq_batch {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Batch.decompositionCost G := by rfl

end
end ErdosGallai

end

end
end

end OAI
