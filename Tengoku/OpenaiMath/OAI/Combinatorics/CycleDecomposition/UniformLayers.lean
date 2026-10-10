import Tengoku.OpenaiMath.OAI.Combinatorics.CycleDecomposition.CostRegrouping

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

structure Layers (P : AssignedPiece V) (Dstar : ℝ) where
  system : SplitSystem V
  count : ℕ
  positive : 0 < count
  cutoff : ∀ j < count, Dstar ≤ inductionScale P.vertices.card j
  last_lt : inductionScale P.vertices.card count < Dstar
  bounded : ∀ j < count, ∀ Q ∈ advance system 0 j [P],
    (system j Q).Bounded (inductionScale P.vertices.card j)
  degree : ∀ j ≤ count, ∀ Q ∈ advance system 0 j [P],
    2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j

theorem uniform_layers : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V),
    Dstar ≤ (P.vertices.card:ℝ) → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card →
    Nonempty (Layers P Dstar) := by
  obtain ⟨Dsp,hsp⟩ := scale_splitter
  refine ⟨max Dsp 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro Dstar hD V _ _ P hn hdeg
  have hD1 : 1 < Dstar := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) ((le_max_right _ _).trans hD)
  have hn1 : 1 < (P.vertices.card:ℝ) := hD1.trans_le hn
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  obtain ⟨split,hsplit⟩ := hsp V
  let s : SplitSystem V := fun j Q => split (inductionScale P.vertices.card j) Q
  have hs : ∀ j Q, Dstar ≤ inductionScale P.vertices.card j → Q.vertices.Nonempty →
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j →
      (s j Q).Bounded (inductionScale P.vertices.card j) := by
    intro j Q hj hQ hd
    exact hsplit _ ((le_max_left _ _).trans (hD.trans hj)) Q hQ hd
  obtain ⟨m,hm,hlast,hcut⟩ := inductionScale_first_cutoff P.vertices.card Dstar hD1 hn
  have hL : ∀ Q ∈ [P], Q.vertices.Nonempty := by simpa using hne
  have hLd : ∀ Q ∈ [P], 2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card 0 := by
    simpa only [List.mem_singleton,forall_eq,inductionScale_zero] using hdeg
  refine ⟨{ system := s, count := m, positive := hm, cutoff := hcut, last_lt := hlast, bounded := ?_, degree := ?_ }⟩
  · intro j hj
    simpa only [Nat.zero_add] using advance_bounded s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))
  · intro j hj
    simpa only [Nat.zero_add] using advance_valid s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))

variable {P : AssignedPiece V} {Dstar : ℝ}

abbrev Layers.frontier (H : Layers P Dstar) (j : ℕ) := advance H.system 0 j [P]
abbrev Layers.scale (_H : Layers P Dstar) (j : ℕ) := inductionScale (P.vertices.card:ℝ) j
abbrev Layers.mass (H : Layers P Dstar) (j : ℕ) := vertexMass (H.frontier j)
abbrev Layers.pieceMass (H : Layers P Dstar) (j : ℕ) := vertexMass (levelPieces H.system j (H.frontier j))

lemma Layers.mass_lower (H : Layers P Dstar) (j) : (P.vertices.card:ℝ) ≤ H.mass j :=
  advance_mass_lower H.system 0 j P

lemma Layers.subset (H : Layers P Dstar) (j) : ∀ Q ∈ H.frontier j, Q.vertices ⊆ P.vertices :=
  advance_subset H.system 0 j [P] P.vertices (by simp)

lemma Layers.box_subset (H : Layers P Dstar) (j) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier j) (hB : B ∈ (H.system j Q).boxes) : B.vertices ⊆ P.vertices :=
  ((H.system j Q).box_subset B hB).trans (H.subset j Q hQ)

lemma Layers.boundary_order (H : Layers P Dstar) (j) (hj : j < H.count)
    {Q : AssignedPiece V} (hQ : Q ∈ H.frontier (j+1)) :
    (Q.vertices.card:ℝ) ≤ (H.scale j)^(51/50:ℝ) := by
  simp only [Layers.frontier,advance_succ,Nat.zero_add] at hQ
  obtain ⟨T,hT,B,hB,hv,_⟩ := (nextLayer_mem H.system j _ Q).mp hQ
  rw [hv]
  exact (H.bounded j hj T hT).2.2.1 B hB

lemma Layers.gap_order (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i)
    (hik : i+200 < H.count) {Q B R : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes)
    (hR : R ∈ advance H.system (i+1) 200 [(H.system i Q).rest B]) :
    (R.vertices.card:ℝ) ≤ (H.scale i)^(1/1000:ℝ) ∧
      2*(edgeCount R.graph:ℝ)/R.vertices.card ≤ (H.scale i)^(1/1000:ℝ) := by
  have hr := advance_local_mem H.system i 200 [P] hQ hB R hR
  have hr' : R ∈ H.frontier ((i+200)+1) := by convert hr using 1
  have hd : 1 < H.scale i := inductionScale_gt_one P.vertices.card hn i
  constructor
  · have hh := H.boundary_order (i+200) hik hr'
    apply hh.trans
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity),← Real.rpow_mul (by linarith : 0 ≤ inductionScale P.vertices.card i)]
    apply Real.rpow_le_rpow_of_exponent_le hd.le
    nlinarith [inductionScale_window.1]
  · have hh := H.degree ((i+200)+1) (by omega) R hr'
    apply hh.trans
    rw [show i+200+1=i+201 by omega]
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hd.le inductionScale_window.2.le

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

lemma disjoint_subset_mass {V A : Type} [Fintype A] [DecidableEq V]
    (U : A → Finset V) (Y : Finset V) (hd : Pairwise fun r s => Disjoint (U r) (U s))
    (hu : ∀ r, U r ⊆ Y) : (∑ r, ((U r).card:ℝ)) ≤ Y.card := by
  have hc : (univ.biUnion U).card = ∑ r, (U r).card := Finset.card_biUnion (fun i _ j _ hij => hd hij)
  have hs : univ.biUnion U ⊆ Y := by
    intro v hv
    obtain ⟨r,_,hv⟩ := Finset.mem_biUnion.mp hv
    exact hu r hv
  have hh := Finset.card_le_card hs
  rw [hc] at hh
  exact_mod_cast hh

end
end ErdosGallai

end
end
end

end OAI
