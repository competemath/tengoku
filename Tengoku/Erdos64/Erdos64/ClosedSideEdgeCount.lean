import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The edges of two closed sides meeting only at a root partition the ambient
edge set. The sides include the root, so their counts include its attachments.
No minimality, degree, or equal-order assumption is needed for this identity.
@isnad1 id=eq.4h5v.s9.c6d08acb68cb from=translated src=- shape=6d60f48f vocab=4e140237
-/
theorem closed_sides_edge_count
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (A B : Finset V) (r : V)
    (hpartition : A ∪ B = Finset.univ)
    (hinter : A ∩ B = {r})
    (hclosedA : ∀ x, x ∈ A → x ≠ r → ∀ y, G.Adj x y → y ∈ A)
    (hclosedB : ∀ x, x ∈ B → x ≠ r → ∀ y, G.Adj x y → y ∈ B) :
    G.edgeFinset.card = (G.induce (↑A : Set V)).edgeFinset.card +
      (G.induce (↑B : Set V)).edgeFinset.card := by
  classical
  let EA := G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  let EB := G.edgeFinset.filter (fun e => e.toFinset ⊆ B)
  have hcover : ∀ v, v ∈ A ∨ v ∈ B := by
    intro v
    have hv : v ∈ A ∪ B := by rw [hpartition]; exact Finset.mem_univ v
    exact Finset.mem_union.mp hv
  have hroot : r ∈ A ∧ r ∈ B := by
    have hr : r ∈ A ∩ B := by rw [hinter]; simp
    exact Finset.mem_inter.mp hr
  have hunion : EA ∪ EB = G.edgeFinset := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · exact (Finset.mem_filter.mp he).1
      · exact (Finset.mem_filter.mp he).1
    · induction e using Sym2.inductionOn with
      | hf x y =>
        intro he
        have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
        have hside : (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
          by_cases hxr : x = r
          · subst x
            rcases hcover y with hy | hy
            · exact Or.inl ⟨hroot.1, hy⟩
            · exact Or.inr ⟨hroot.2, hy⟩
          · rcases hcover x with hx | hx
            · exact Or.inl ⟨hx, hclosedA x hx hxr y hxy⟩
            · exact Or.inr ⟨hx, hclosedB x hx hxr y hxy⟩
        simpa only [EA, EB, Finset.mem_union, Finset.mem_filter,
          Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff, he, true_and] using hside
  have hdisjoint : Disjoint EA EB := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    induction e using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨he, hA⟩ := Finset.mem_filter.mp heA
      obtain ⟨_, hB⟩ := Finset.mem_filter.mp heB
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
      have hx : x ∈ A ∩ B := by
        exact Finset.mem_inter.mpr ⟨hA (by simp), hB (by simp)⟩
      have hy : y ∈ A ∩ B := by
        exact Finset.mem_inter.mpr ⟨hA (by simp), hB (by simp)⟩
      rw [hinter, Finset.mem_singleton] at hx hy
      exact hxy.ne (hx.trans hy.symm)
  calc
    G.edgeFinset.card = (EA ∪ EB).card := congrArg Finset.card hunion.symm
    _ = EA.card + EB.card := Finset.card_union_of_disjoint hdisjoint
    _ = _ := by
      rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset,
        SimpleGraph.card_filter_edgeFinset_toFinset_subset]

end Erdos64
