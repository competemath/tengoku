import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedContraction
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Minor
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vertex accounting for a family of contracted blocks
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

/--
@isnad1 id=eq.0h3v.s5.ecb62dae5d9b from=translated src=- shape=852b97b7 vocab=2b57e1e9
-/
theorem ConnectedBlockFamily.covered_card_eq_sum :
    F.covered.card = ∑ B ∈ F.blocks, B.card := by
  classical
  have hpair : (F.blocks : Set (Finset V)).PairwiseDisjoint id := by
    intro B hB C hC hBC
    exact Finset.disjoint_coe.mp (F.disjoint B hB C hC hBC)
  exact Finset.card_biUnion hpair

/--
@isnad1 id=eq.0h3v.s7.dc9744f039b9 from=translated src=- shape=37f55615 vocab=fe80557a
-/
theorem ConnectedBlockFamily.vertex_card_eq :
    Fintype.card F.Vertex = F.blocks.card + F.coveredᶜ.card := by
  classical
  rw [Fintype.card_sum]
  have hblocks : Fintype.card ↥(F.blocks : Set (Finset V)) =
      F.blocks.card := by simpa using Fintype.card_coe F.blocks
  have houtside : Fintype.card {v : V // v ∉ F.covered} =
      F.coveredᶜ.card := by
    simpa using Fintype.card_coe F.coveredᶜ
  rw [hblocks, houtside]

/--
@isnad1 id=eq.0h3v.s7.ee86a2418816 from=translated src=- shape=824e9142 vocab=c3cb4153
-/
theorem ConnectedBlockFamily.vertex_card_add_covered :
    Fintype.card F.Vertex + F.covered.card =
      Fintype.card V + F.blocks.card := by
  rw [F.vertex_card_eq]
  have hcompl := Finset.card_compl_add_card F.covered
  omega

/--
@isnad1 id=eq.2h4v.s7.3a00f973e9fe from=translated src=- shape=4ca76345 vocab=d643daf4
-/
theorem ConnectedBlockFamily.vertex_card_add_savings
    (hsize : ∀ B ∈ F.blocks, B.card = h)
    (hh : 1 ≤ h) :
    Fintype.card F.Vertex + F.blocks.card * (h - 1) =
      Fintype.card V := by
  have hcovered : F.covered.card = F.blocks.card * h := by
    rw [F.covered_card_eq_sum]
    calc
      (∑ B ∈ F.blocks, B.card) = ∑ B ∈ F.blocks, h := by
        apply Finset.sum_congr rfl
        intro B hB
        exact hsize B hB
      _ = F.blocks.card * h := by simp [Nat.mul_comm]
  have hcount := F.vertex_card_add_covered
  rw [hcovered] at hcount
  have hstep : h - 1 + 1 = h := Nat.sub_add_cancel hh
  have hmul : F.blocks.card * h =
      F.blocks.card * (h - 1) + F.blocks.card := by
    conv_lhs => rw [← hstep]
    ring
  omega

/--
@isnad1 id=not.1h4v.s5.509697a86692 from=translated src=- shape=854c7997 vocab=05ba5ce6
-/
theorem ConnectedBlockFamily.quotient_cliqueMinor_free
    (t : ℕ) (hG : ¬ HasCliqueMinor G t) :
    ¬ HasCliqueMinor F.quotient t := by
  intro hq
  exact hG (hasCliqueMinor_of_minor F.quotient_isMinor hq)

end HadwigerLean
