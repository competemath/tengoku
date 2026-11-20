import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The smaller member of a two-sided cut-root partition is a genuine
rooted side.  The criticality and opposite-side degree premises are exposed
for later descent use; this theorem only packages the side itself.-/
theorem exists_unequal_cut_root_side
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (_hcritical : IsSubgraphCritical G)
    (A B : Finset V) (r : V)
    (hpartition : A ∪ B = Finset.univ)
    (hinter : A ∩ B = ({r} : Finset V))
    (hnocross : ∀ x, x ∈ A → x ≠ r →
      ∀ y, y ∈ B → y ≠ r → ¬G.Adj x y)
    (hrootA : 2 ≤ internalDegree G A r)
    (_hrootB : 2 ≤ internalDegree G B r)
    (hAB : A.card < B.card) :
    ∃ (S : Finset V) (root : {v : V // v ∈ S}),
      (∀ v, v ∈ S → v ≠ root.1 → ∀ w, G.Adj v w → w ∈ S) ∧
      2 ≤ internalDegree G S root.1 ∧
      2 * S.card - 1 < Fintype.card V := by
  classical
  have hrA : r ∈ A := by
    have hr : r ∈ A ∩ B := by
      rw [hinter]
      simp
    exact (Finset.mem_inter.mp hr).1
  have hclosedA : ∀ v, v ∈ A → v ≠ r →
      ∀ w, G.Adj v w → w ∈ A := by
    intro v hvA hvr w hvw
    have hwpart : w ∈ A ∨ w ∈ B := by
      have hw : w ∈ A ∪ B := by
        rw [hpartition]
        exact Finset.mem_univ w
      exact Finset.mem_union.mp hw
    rcases hwpart with hwA | hwB
    · exact hwA
    · by_cases hwr : w = r
      · simpa [hwr] using hrA
      · exact (hnocross v hvA hvr w hwB hwr hvw).elim
  have hcard_identity : Fintype.card V + 1 = A.card + B.card := by
    have hcard := Finset.card_union_add_card_inter A B
    rw [hpartition, hinter] at hcard
    simpa using hcard
  refine ⟨A, ⟨r, hrA⟩, hclosedA, hrootA, ?_⟩
  have hAB' : A.card + 1 ≤ B.card := Nat.succ_le_of_lt hAB
  have hAB'' : A.card + (A.card + 1) ≤ A.card + B.card :=
    Nat.add_le_add_left hAB' A.card
  have hsum' : A.card + B.card = Fintype.card V + 1 :=
    hcard_identity.symm
  have htw : 2 * A.card + 1 ≤ Fintype.card V + 1 := by
    calc
      2 * A.card + 1 = A.card + (A.card + 1) := by omega
      _ ≤ A.card + B.card := hAB''
      _ = Fintype.card V + 1 := hsum'
  have htw' : 2 * A.card ≤ Fintype.card V := by
    exact Nat.le_of_succ_le_succ (by simpa [Nat.succ_eq_add_one,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htw)
  have hAcard_filter : internalDegree G A r ≤ A.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hAcard : 2 ≤ A.card := le_trans hrootA hAcard_filter
  omega

end Erdos64
