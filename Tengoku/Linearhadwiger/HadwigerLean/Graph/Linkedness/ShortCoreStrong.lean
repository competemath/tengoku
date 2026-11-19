import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.ShortCoreFinal
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Retaining the degree guarantee of the linked residual core
-/

namespace HadwigerLean
namespace Linkedness

set_option maxHeartbeats 1000000

/-- The small side of an anticomplete dense partition retains minimum
degree five times k, in addition to being k-linked.
@isnad1 id=ex.7h5v.s8.01f0e66154b4 from=translated src=- shape=255c9070 vocab=1c75f73e
-/
theorem dense_linked_side_of_anticomplete_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (horder : Fintype.card V ≤ 14 * k)
    (hdegree : ∀ v, 5 * k ≤ G.degree v)
    (A B : Finset V)
    (hcover : A ∪ B = Finset.univ)
    (hdisjoint : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hnoedge : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    ∃ S : Finset V, S.Nonempty ∧ S.card ≤ 7 * k ∧
      (∀ v : (S : Set V), 5 * k ≤ (G.induce (S : Set V)).degree v) ∧
      KLinked (G.induce (S : Set V)) k := by
  classical
  have hsum : A.card + B.card = Fintype.card V := by
    have hcard := Finset.card_union_of_disjoint hdisjoint
    rw [hcover] at hcard
    simpa only [Finset.card_univ] using hcard.symm
  have hcoverSet : (A : Set V) ∪ (B : Set V) = Set.univ := by
    simpa using congrArg (fun s : Finset V => (s : Set V)) hcover
  have hsmall : A.card ≤ 7 * k ∨ B.card ≤ 7 * k := by omega
  rcases hsmall with hA_small | hB_small
  · have hdegA : ∀ v : (A : Set V), 5 * k ≤
        (G.induce (A : Set V)).degree v := by
      intro v
      rw [degree_induce_of_anticomplete_partition G (A : Set V) (B : Set V)
        hcoverSet hnoedge v]
      exact hdegree v.1
    refine ⟨A, hA, hA_small, hdegA, ?_⟩
    exact kLinked_of_five_k_degree_seven_k_order
      (G.induce (A : Set V)) k hdegA (by simpa using hA_small)
  · have hnoedge' : ∀ x ∈ B, ∀ y ∈ A, ¬ G.Adj x y := by
      intro x hx y hy hxy
      exact hnoedge y hy x hx hxy.symm
    have hcover' : (B : Set V) ∪ (A : Set V) = Set.univ := by
      simpa only [Set.union_comm] using hcoverSet
    have hdegB : ∀ v : (B : Set V), 5 * k ≤
        (G.induce (B : Set V)).degree v := by
      intro v
      rw [degree_induce_of_anticomplete_partition G (B : Set V) (A : Set V)
        hcover' hnoedge' v]
      exact hdegree v.1
    refine ⟨B, hB, hB_small, hdegB, ?_⟩
    exact kLinked_of_five_k_degree_seven_k_order
      (G.induce (B : Set V)) k hdegB (by simpa using hB_small)

/-- The dense linked side has at least twice k vertices.
@isnad1 id=le.2h4v.s8.9ba3a5ba0789 from=translated src=- shape=3abb7044 vocab=e1749101
-/
theorem dense_linked_side_card_ge_two_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (S : Finset V) (hS : S.Nonempty)
    (hdegree : ∀ v : (S : Set V),
      5 * k ≤ (G.induce (S : Set V)).degree v) :
    2 * k ≤ S.card := by
  classical
  obtain ⟨v,hv⟩ := hS
  let w : (S : Set V) := ⟨v,hv⟩
  have hlt := (G.induce (S : Set V)).degree_lt_card_verts w
  have hcard : Fintype.card (S : Set V) = S.card := by simp
  have hdeg := hdegree w
  omega

/-- A disconnected residual graph meeting the 14k/5k bounds contains a
linked side retaining the five-k degree guarantee.
@isnad1 id=ex.3h5v.s8.be5631907d2a from=translated src=- shape=435c91f3 vocab=55ba9629
-/
theorem dense_linked_side_of_nonreachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (horder : Fintype.card V ≤ 14 * k)
    (hdegree : ∀ x, 5 * k ≤ H.degree x)
    (u v : V) (huv : ¬ H.Reachable u v) :
    ∃ S : Finset V, S.Nonempty ∧ 2 * k ≤ S.card ∧ S.card ≤ 7 * k ∧
      (∀ x : (S : Set V), 5 * k ≤ (H.induce (S : Set V)).degree x) ∧
      KLinked (H.induce (S : Set V)) k := by
  classical
  let A : Finset V := Finset.univ.filter (fun x => H.Reachable u x)
  let B : Finset V := Aᶜ
  have hcover : A ∪ B = Finset.univ := Finset.union_compl A
  have hdisjoint : Disjoint A B := by
    change Disjoint A Aᶜ
    exact disjoint_compl_right
  have hnoedge : ∀ x ∈ A, ∀ y ∈ B, ¬ H.Adj x y := by
    intro x hx y hy hxy
    have hux : H.Reachable u x := (Finset.mem_filter.mp hx).2
    have huy : H.Reachable u y := hux.trans hxy.reachable
    have hyA : y ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huy⟩
    exact (Finset.mem_compl.mp hy) hyA
  have hA : A.Nonempty := by
    refine ⟨u, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl u⟩
  have hB : B.Nonempty := by
    refine ⟨v, ?_⟩
    apply Finset.mem_compl.mpr
    intro hvA
    exact huv (Finset.mem_filter.mp hvA).2
  obtain ⟨S,hSnon,hScard,hSdeg,hSlinked⟩ :=
    dense_linked_side_of_anticomplete_partition H k horder hdegree
      A B hcover hdisjoint hA hB hnoedge
  exact ⟨S,hSnon,dense_linked_side_card_ge_two_mul H k S hSnon hSdeg,
    hScard,hSdeg,hSlinked⟩

namespace ShortPartial

end ShortPartial

end Linkedness
end HadwigerLean
