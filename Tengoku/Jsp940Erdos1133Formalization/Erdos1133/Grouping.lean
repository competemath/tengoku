import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Finite grouping of indexed samples. Coincident sample locations remain
distinct indices: no injectivity assumption on a later node map is used.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1133

variable {α : Type*} [DecidableEq α]

/-- Split a finite set into disjoint `k`-element groups, discarding fewer than `k`
indices. The groups are actual subsets of the original index set.-/
theorem exists_disjoint_equal_groups (s : Finset α) (k : ℕ) (hk : 0 < k) :
    ∃ G : Finset (Finset α),
      (∀ g ∈ G, g ⊆ s ∧ g.card = k) ∧
      (G : Set (Finset α)).Pairwise Disjoint ∧ s.card ≤ k * G.card + (k - 1) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hsmall : s.card < k
    · refine ⟨∅, by simp, by simp, ?_⟩
      simp only [Finset.card_empty, mul_zero, zero_add]
      omega
    · have hks : k ≤ s.card := Nat.le_of_not_gt hsmall
      obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hks
      have htpos : 0 < t.card := by omega
      have htnonempty : t.Nonempty := Finset.card_pos.mp htpos
      have hstrict : s \ t ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨a, ha⟩ := htnonempty
        have hmem : a ∈ s \ t := heq.symm ▸ hts ha
        exact (Finset.mem_sdiff.mp hmem).2 ha
      obtain ⟨G, hG, hdis, hbudget⟩ := ih (s \ t) hstrict
      have htG : t ∉ G := by
        intro ht
        obtain ⟨a, ha⟩ := htnonempty
        exact (Finset.mem_sdiff.mp ((hG t ht).1 ha)).2 ha
      refine ⟨insert t G, ?_, ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact ⟨hts, htcard⟩
        · exact ⟨(hG g hg).1.trans Finset.sdiff_subset, (hG g hg).2⟩
      · intro g hg h hh hgh
        by_cases hgt : g = t
        · subst g
          have hhG : h ∈ G := (Finset.mem_insert.mp hh).resolve_left hgh.symm
          apply Finset.disjoint_left.mpr
          intro a hat hah
          exact (Finset.mem_sdiff.mp ((hG h hhG).1 hah)).2 hat
        · have hgG : g ∈ G := (Finset.mem_insert.mp hg).resolve_left hgt
          by_cases hht : h = t
          · subst h
            apply Finset.disjoint_left.mpr
            intro a hag hat
            exact (Finset.mem_sdiff.mp ((hG g hgG).1 hag)).2 hat
          · have hhG : h ∈ G := (Finset.mem_insert.mp hh).resolve_left hht
            exact hdis hgG hhG hgh
      · rw [Finset.card_insert_of_notMem htG]
        have hcard : (s \ t).card = s.card - k := by
          rw [Finset.card_sdiff_of_subset hts, htcard]
        rw [hcard] at hbudget
        nlinarith [Nat.sub_add_cancel hks]

/-- A group containing only one bin cannot also belong to a different bin's
family, because all groups have positive size.-/
theorem exists_grouping_by_bins {β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset α) (b : α → β) (k : ℕ) (hk : 0 < k) :
    ∃ G : Finset (Finset α),
      (∀ g ∈ G, g ⊆ s ∧ g.card = k ∧ ∃ j : β, ∀ a ∈ g, b a = j) ∧
      (G : Set (Finset α)).Pairwise Disjoint ∧
      s.card ≤ k * G.card + (k - 1) * Fintype.card β := by
  classical
  have hex (j : β) := exists_disjoint_equal_groups (s.filter fun a => b a = j) k hk
  choose G hG hdis hbudget using hex
  have hmono (j : β) (g : Finset α) (hg : g ∈ G j) :
      g ⊆ s ∧ g.card = k ∧ ∀ a ∈ g, b a = j := by
    refine ⟨(hG j g hg).1.trans (Finset.filter_subset _ _), (hG j g hg).2, ?_⟩
    exact fun a ha => (Finset.mem_filter.mp ((hG j g hg).1 ha)).2
  have hcross (i j : β) (hij : i ≠ j) (g : Finset α) (hg : g ∈ G i)
      (h : Finset α) (hh : h ∈ G j) : Disjoint g h := by
    apply Finset.disjoint_left.mpr
    intro a hag hah
    exact hij (((hmono i g hg).2.2 a hag).symm.trans ((hmono j h hh).2.2 a hah))
  have hfamily : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint G := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    have hgcard := (hmono i g hgi).2.1
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < g.card by omega)
    exact Finset.disjoint_left.mp (hcross i j hij g hgi g hgj) ha ha
  let groups := Finset.univ.biUnion G
  have hgroupscard : groups.card = ∑ j, (G j).card := by
    exact Finset.card_biUnion hfamily
  refine ⟨groups, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨hgs, hgcard, hjg⟩ := hmono j g hgj
    exact ⟨hgs, hgcard, j, hjg⟩
  · intro g hg h hh hgh
    obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨j, hj, hhj⟩ := Finset.mem_biUnion.mp hh
    by_cases hij : i = j
    · subst j
      exact hdis i hgi hhj hgh
    · exact hcross i j hij g hgi h hhj
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbudget j)
    have hpartition : (∑ j : β, (s.filter fun a => b a = j).card) = s.card := by
      have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.univ)
        (f := b) (by simp)
      exact h.symm
    rw [hpartition, Finset.sum_add_distrib, ← Finset.mul_sum, ← hgroupscard] at hsum
    simpa [mul_comm] using hsum

/-- The finite-index form used by the angular-bin proof.-/
theorem group_indices {n N k : ℕ} (b : Fin n → Fin N) (hk : 0 < k) :
    ∃ G : Finset (Finset (Fin n)),
      (∀ g ∈ G, g.card = k ∧ ∃ j : Fin N, ∀ i ∈ g, b i = j) ∧
      (G : Set (Finset (Fin n))).Pairwise Disjoint ∧ n - (k - 1) * N ≤ k * G.card := by
  obtain ⟨G, hG, hd, hb⟩ := exists_grouping_by_bins Finset.univ b k hk
  refine ⟨G, fun g hg => (hG g hg).2, hd, ?_⟩
  simp only [Finset.card_univ, Fintype.card_fin] at hb
  omega

/-- Independently selected local data on disjoint groups define one global
label vector, before any approximating polynomial is considered.-/
theorem glue_group_labels (G : Finset (Finset α))
    (hdis : (G : Set (Finset α)).Pairwise Disjoint)
    (a : Finset α → α → ℝ) (ha : ∀ g ∈ G, ∀ i ∈ g, |a g i| ≤ 1) :
    ∃ y : α → ℝ, (∀ i, |y i| ≤ 1) ∧ ∀ g ∈ G, ∀ i ∈ g, y i = a g i := by
  classical
  let occurs (i : α) : Prop := ∃ g ∈ G, i ∈ g
  let y (i : α) : ℝ := if hi : occurs i then a (Classical.choose hi) i else 0
  have hchoice (i : α) (hi : occurs i) :
      Classical.choose hi ∈ G ∧ i ∈ Classical.choose hi := Classical.choose_spec hi
  refine ⟨y, ?_, ?_⟩
  · intro i
    by_cases hi : occurs i
    · dsimp [y]
      rw [dite_eq_left hi]
      exact ha _ (hchoice i hi).1 i (hchoice i hi).2
    · simp [y, hi]
  · intro g hg i hi
    have hocc : occurs i := ⟨g, hg, hi⟩
    have hchosen : Classical.choose hocc = g := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdis (hchoice i hocc).1 hg hne)
        (hchoice i hocc).2 hi
    dsimp [y]
    rw [dite_eq_left hocc, hchosen]

/-- One error in every disjoint group forces at least as many erroneous indices
as there are groups. This counts indices even when their sample locations agree.-/
theorem groups_force_errors (s : Finset α) (G : Finset (Finset α))
    (hinside : ∀ g ∈ G, g ⊆ s) (hdis : (G : Set (Finset α)).Pairwise Disjoint)
    (Bad : α → Prop) [DecidablePred Bad]
    (hbad : ∀ g ∈ G, ∃ i ∈ g, Bad i) : G.card ≤ (s.filter Bad).card := by
  classical
  choose a ha hBa using fun g : G => hbad g.val g.property
  let f : G → (s.filter Bad) := fun g =>
    ⟨a g, Finset.mem_filter.mpr ⟨hinside g.val g.property (ha g), hBa g⟩⟩
  have hf : Function.Injective f := by
    intro g h heq
    apply Subtype.ext
    by_contra hgh
    have hai : a g = a h := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp (hdis g.property h.property hgh) (ha g) (hai ▸ ha h)
  simpa using Fintype.card_le_of_injective f hf

end Erdos1133
