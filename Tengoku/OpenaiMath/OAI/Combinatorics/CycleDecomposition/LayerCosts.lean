import Tengoku.OpenaiMath.OAI.Combinatorics.CycleDecomposition.UniformLayers

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
variable {V : Type} [Fintype V] [DecidableEq V]

lemma assigned_union_edges (L : List (AssignedPiece V)) :
    (⋃ i : Fin L.length, (L.get i).graph.edgeSet) = (graphUnion (L.map AssignedPiece.graph)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet]

    rw [graphUnion_adj]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨_,List.mem_map.mpr ⟨_,L.get_mem i,rfl⟩,hi⟩
    · rintro ⟨G,hG,hxy⟩
      obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hG
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hQ
      exact ⟨i,hxy⟩

lemma box_coupled_partition {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph) := by
  apply graphPartition_of_le_one
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
  split_ifs at hb hr <;> omega

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma pastPieces_mem (s : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V))
    {R : AssignedPiece V} (hR : R ∈ pastPieces s j k L) :
    ∃ l < k, R ∈ levelPieces s (j+l) (advance s j l L) := by
  induction k with
  | zero => simp [pastPieces] at hR
  | succ k ih =>
    rcases List.mem_append.mp hR with h | h
    · obtain ⟨l,hl,hR⟩ := ih h
      exact ⟨l,by omega,hR⟩
    · exact ⟨k,by omega,h⟩

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Real

lemma main_gap_scalar (q n S M L Nt Ni C t w : ℝ)
    (hn : 0 ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C) (ht : 0 ≤ t) (hw : 0 < w)
    (hM : M ≤ mainP*S) (hL : L ≤ mainH*n/w)
    (hNt : Nt ≤ n+mainH*n/w) (hNilo : n ≤ Ni) (hNihi : Ni ≤ 2*n)
    (hq : q ≤ L+(9+C*mainEta)*M+(t+8)*Nt+(8-t/3)*S+((2/3)*t/w-8)*Ni) :
    q ≤ mainA₂*(S+n/w)+(C/100)*S+t*(n-S/3+mainA₁*n/w) := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hT := mul_le_mul_of_nonneg_left hNt (by linarith : 0 ≤ t+8)
  have hI := mul_le_mul_of_nonneg_left hNihi (by positivity : 0 ≤ (2/3)*t/w)
  have hI' : -8*Ni ≤ -8*n := by linarith
  have hA := mul_le_mul_of_nonneg_right (le_max_left (9*mainP+8) (9*mainH)) hS
  have hB := mul_le_mul_of_nonneg_right (le_max_right (9*mainP+8) (9*mainH)) (div_nonneg hn hw.le)
  change (9*mainP+8)*S ≤ mainA₂*S at hA
  change 9*mainH*(n/w) ≤ mainA₂*(n/w) at hB
  simp only [mainEta,mainP,mainA₁,div_eq_mul_inv] at hc hT hI hI' hA hB hq hL ⊢
  nlinarith only [hc,hT,hI,hI',hA,hB,hq,hL]

lemma main_terminal_scalar (q n M C Dstar : ℝ) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hCbig : 4*(20+Dstar+18*mainP) ≤ C) (hM : M ≤ 2*mainP*n)
    (hq : q ≤ (20+Dstar)*n+(9+C*mainEta)*M) :
    q ≤ C*Batch.inductionPhi n*n := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hbig := mul_le_mul_of_nonneg_right hCbig hn
  have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).1 (mul_nonneg hC hn)
  have hCn : 0 ≤ C*n := mul_nonneg hC hn
  simp only [mainEta,mainP] at hc hbig hq
  nlinarith only [hq,hc,hbig,hphi,hCn]

end
end ErdosGallai

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.gap_log (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i) :
    logb 2 (H.scale (i+200)) = scaleTheta^200 * logb 2 (H.scale i) := by
  dsimp only [Layers.scale]
  rw [inductionScale_add _ (by positivity)]
  exact Real.logb_rpow_eq_mul_logb_of_pos (inductionScale_pos _ (by linarith) _)

end
end ErdosGallai.Scale

end
end
end

end OAI
