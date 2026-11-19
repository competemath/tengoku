import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedEmpty
import Tengoku.Linearhadwiger.HadwigerLean.Graph.SmallConnected.PackedCount
import Tengoku.Seed.Order.Preorder.Finite
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A maximal family of low-loss connected blocks
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An admissible family has uniform block size and total contraction
loss at most `p` times the number of removed vertices.-/
noncomputable def GoodPackedFamily
    (G : SimpleGraph V) (h p : ℕ) (F : ConnectedBlockFamily G) : Prop := by
  classical
  exact (∀ B ∈ F.blocks, B.card = h) ∧
    edgeCount G ≤ edgeCount F.quotient + p * F.blocks.card * (h - 1) ∧
    edgeCount F.quotient ≤ edgeCount G

/--
@isnad1 id=goodpack.0h4v.s4.fe270565b787 from=translated src=- shape=b23b412d vocab=383f3326
-/
theorem goodPackedFamily_empty
    (G : SimpleGraph V) (h p : ℕ) :
    GoodPackedFamily G h p (emptyConnectedBlockFamily G) := by
  classical
  unfold GoodPackedFamily
  constructor
  · intro B hB
    simp [emptyConnectedBlockFamily] at hB
  · constructor
    · change edgeCount G ≤
        edgeCount (emptyConnectedBlockFamily G).quotient + p * 0 * (h - 1)
      simpa [emptyConnectedBlockFamily_edgeCount]
    · exact le_of_eq (emptyConnectedBlockFamily_edgeCount G)

/-- Finite maximality of the number of admissible disjoint blocks.
@isnad1 id=ex.0h4v.s5.983353acbad7 from=translated src=- shape=e446cf65 vocab=64572976
-/
theorem exists_maximal_good_packed_family
    (G : SimpleGraph V) (h p : ℕ) :
    ∃ F : ConnectedBlockFamily G,
      GoodPackedFamily G h p F ∧
      ∀ F' : ConnectedBlockFamily G,
        GoodPackedFamily G h p F' → F'.blocks.card ≤ F.blocks.card := by
  classical
  let P : Set (Finset (Finset V)) :=
    {B | ∃ F : ConnectedBlockFamily G,
      F.blocks = B ∧ GoodPackedFamily G h p F}
  have hfinite : P.Finite := Set.toFinite P
  have hnonempty : P.Nonempty := by
    refine ⟨∅, ?_⟩
    exact ⟨emptyConnectedBlockFamily G, rfl, goodPackedFamily_empty G h p⟩
  obtain ⟨B, hB, hmax⟩ :=
    hfinite.exists_maximalFor (fun B : Finset (Finset V) => B.card) P hnonempty
  obtain ⟨F, hFB, hgood⟩ := hB
  refine ⟨F, hgood, ?_⟩
  intro F' hgood'
  by_contra hnot
  have hlt : F.blocks.card < F'.blocks.card := Nat.lt_of_not_ge hnot
  have hP' : F'.blocks ∈ P := ⟨F', rfl, hgood'⟩
  have hle : B.card ≤ F'.blocks.card := by simpa [← hFB] using hlt.le
  have hback := hmax hP' hle
  change F'.blocks.card ≤ B.card at hback
  rw [← hFB] at hback
  omega

/-- An admissible family of `h`-sets removes at most `N` vertices.
@isnad1 id=le.2h5v.s6.1262e3269cf6 from=translated src=- shape=dc841c67 vocab=cf3346fc
-/
theorem GoodPackedFamily.savings_le_card
    (G : SimpleGraph V) (h p : ℕ) (hh : 1 ≤ h)
    (F : ConnectedBlockFamily G) (hF : GoodPackedFamily G h p F) :
    F.blocks.card * (h - 1) ≤ Fintype.card V := by
  have hsize := hF.1
  have hcard := F.vertex_card_add_savings hsize hh
  omega

/-- Exact initial edge count and admissibility imply at least 90 percent
of the original edges survive the simultaneous contraction.
@isnad1 id=le.4h6v.s6.3509ecddb1aa from=translated src=- shape=7f001ec8 vocab=a5a03087
-/
theorem GoodPackedFamily.retained_edges
    (G : SimpleGraph V) (h p : ℕ) (hh : 1 ≤ h)
    (F : ConnectedBlockFamily G) (hF : GoodPackedFamily G h p F)
    (N : ℕ) (hN : Fintype.card V = N)
    (hexact : edgeCount G = 10 * p * N) :
    9 * p * N ≤ edgeCount F.quotient := by
  classical
  have hsav := hF.savings_le_card G h p hh
  rw [hN] at hsav
  have hmul := Nat.mul_le_mul_left p hsav
  have hgood := hF.2.1
  rw [hexact] at hgood
  nlinarith

end HadwigerLean
