import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TokenGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Token-graph edges as single-token moves

This file proves that the symmetric-difference definition of a token-graph edge is
equivalent to moving one occupied vertex across an edge to an unoccupied vertex.
-/

open scoped symmDiff

namespace BurningPath

variable {V : Type*} [DecidableEq V]

private theorem symmDiff_pair_eq_insert_erase {A : Finset V} {u v : V}
    (hu : u ∈ A) (hv : v ∉ A) :
    A ∆ ({u, v} : Finset V) = insert v (A.erase u) := by
  have huv : u ≠ v := fun h ↦ hv (h ▸ hu)
  ext x
  by_cases hxu : x = u
  · subst x
    simp [Finset.mem_symmDiff, hu, huv]
  by_cases hxv : x = v
  · subst x
    simp [Finset.mem_symmDiff, hv]
  simp [Finset.mem_symmDiff, hxu, hxv]

/--
Two configurations are adjacent in the token graph exactly when one token moves along an
edge of `G` to an unoccupied vertex.-/
theorem tokenGraph_adj_iff_exists_move (G : SimpleGraph V) (k : ℕ)
    (A B : Configuration V k) :
    (tokenGraph G k).Adj A B ↔
      ∃ u ∈ A.1, ∃ v ∉ A.1, G.Adj u v ∧ B.1 = insert v (A.1.erase u) := by
  constructor
  · rw [tokenGraph_adj]
    rintro ⟨p, q, hpq, hAB⟩
    have hpq_ne : p ≠ q := hpq.ne
    have hfin : A.1 ∆ B.1 = ({p, q} : Finset V) := by
      apply Finset.coe_injective
      simpa using hAB
    have htotal : (A.1 ∆ B.1).card = 2 := by
      rw [hfin]
      simp [hpq_ne]
    have hdisjoint : Disjoint (A.1 \ B.1) (B.1 \ A.1) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx hy
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
    have hsum : (A.1 \ B.1).card + (B.1 \ A.1).card = 2 := by
      rw [← Finset.card_union_of_disjoint hdisjoint, ← Finset.symmDiff_def]
      exact htotal
    have hequal : (A.1 \ B.1).card = (B.1 \ A.1).card :=
      Finset.card_sdiff_comm (A.2.trans B.2.symm)
    have hleft : 0 < (A.1 \ B.1).card := by omega
    have hright : 0 < (B.1 \ A.1).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hleft
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hright
    obtain ⟨huA, huB⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hvB, hvA⟩ := Finset.mem_sdiff.mp hv
    have huPair : u = p ∨ u = q := by
      have : u ∈ ({p, q} : Finset V) := by
        rw [← hfin]
        exact Finset.mem_symmDiff.mpr (Or.inl ⟨huA, huB⟩)
      simpa using this
    have hvPair : v = p ∨ v = q := by
      have : v ∈ ({p, q} : Finset V) := by
        rw [← hfin]
        exact Finset.mem_symmDiff.mpr (Or.inr ⟨hvB, hvA⟩)
      simpa using this
    have huv_ne : u ≠ v := fun h ↦ hvA (h ▸ huA)
    have huv : G.Adj u v := by
      rcases huPair with rfl | rfl
      · rcases hvPair with rfl | rfl
        · exact (huv_ne rfl).elim
        · exact hpq
      · rcases hvPair with rfl | rfl
        · exact hpq.symm
        · exact (huv_ne rfl).elim
    have hpairSubset : ({u, v} : Finset V) ⊆ {p, q} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact huPair
      · exact hvPair
    have hpairs : ({u, v} : Finset V) = {p, q} := by
      apply Finset.eq_of_subset_of_card_le hpairSubset
      simp [huv_ne, hpq_ne]
    have hfin' : A.1 ∆ B.1 = ({u, v} : Finset V) :=
      hfin.trans hpairs.symm
    have hB : B.1 = insert v (A.1.erase u) := by
      calc
        B.1 = A.1 ∆ (A.1 ∆ B.1) := (symmDiff_symmDiff_cancel_left A.1 B.1).symm
        _ = A.1 ∆ ({u, v} : Finset V) := by rw [hfin']
        _ = insert v (A.1.erase u) := symmDiff_pair_eq_insert_erase huA hvA
    exact ⟨u, huA, v, hvA, huv, hB⟩
  · rintro ⟨u, huA, v, hvA, huv, hB⟩
    rw [tokenGraph_adj]
    refine ⟨u, v, huv, ?_⟩
    have hfin : A.1 ∆ B.1 = ({u, v} : Finset V) := by
      rw [hB, ← symmDiff_pair_eq_insert_erase huA hvA]
      exact symmDiff_symmDiff_cancel_left A.1 ({u, v} : Finset V)
    simpa using congrArg (fun s : Finset V ↦ (s : Set V)) hfin

omit [DecidableEq V] in
/--
For the witnesses of a token move, the removed endpoint is absent from the target
configuration and the inserted endpoint is present there.-/
theorem tokenGraph_adj_exists_move_membership (G : SimpleGraph V) (k : ℕ)
    (A B : Configuration V k) (h : (tokenGraph G k).Adj A B) :
    ∃ u v, u ∈ A.1 ∧ u ∉ B.1 ∧ v ∉ A.1 ∧ v ∈ B.1 ∧ G.Adj u v := by
  classical
  obtain ⟨u, huA, v, hvA, huv, hB⟩ :=
    (tokenGraph_adj_iff_exists_move G k A B).mp h
  refine ⟨u, v, huA, ?_, hvA, ?_, huv⟩
  · rw [hB]
    simp [huv.ne]
  · rw [hB]
    simp

/-- The same move characterization, oriented from the target configuration.-/
theorem tokenGraph_adj_iff_exists_reverseMove (G : SimpleGraph V) (k : ℕ)
    (A B : Configuration V k) :
    (tokenGraph G k).Adj A B ↔
      ∃ v ∈ B.1, ∃ u ∉ B.1, G.Adj v u ∧ A.1 = insert u (B.1.erase v) := by
  rw [(tokenGraph G k).adj_comm]
  exact tokenGraph_adj_iff_exists_move G k B A

end BurningPath
