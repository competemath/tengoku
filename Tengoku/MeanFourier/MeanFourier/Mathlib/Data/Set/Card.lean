module

public import Tengoku

public section

namespace Set
variable {α β γ : Type*} {f : α → β → γ} {s : Set α} {t : Set β} {k : ℕ}

/--
@isnad1 id=le.2h6v.s5.269d956ed56f from=translated src=- shape=2df3dd4b vocab=0ec41281
-/
lemma ncard_image2_le (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).ncard ≤ s.ncard * t.ncard := by
  grw [← image_uncurry_prod, ncard_image_le (hs.prod ht), ncard_prod]

/--
@isnad1 id=ex.4h4v.s6.b2683ec8fee1 from=translated src=- shape=087df06c vocab=dc5405c3
-/
lemma Infinite.exists_superset_ncard_eq' {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) :
    ∃ s', s'.Finite ∧ s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.sdiff hs).exists_subset_ncard_eq (k - s.ncard)
  refine ⟨s ∪ s₁, hs.union hs₁fin, subset_union_left, union_subset hst (hs₁.trans sdiff_subset), ?_⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]

/--
@isnad1 id=ex.2h3v.s5.675ee393aafd from=translated src=- shape=a87eef45 vocab=587d755e
-/
lemma exists_superset_ncard_eq [Infinite α] (hs : s.Finite) (hsk : s.ncard ≤ k) :
    ∃ t, t.Finite ∧ s ⊆ t ∧ t.ncard = k := by
  simpa using infinite_univ.exists_superset_ncard_eq' s.subset_univ hs hsk

/--
@isnad1 id=ex.2h3v.s5.080a51fda299 from=translated src=- shape=d9736e26 vocab=6e6b3677
-/
lemma exists_subset_ncard_eq (hs : s.Finite) (hks : k ≤ s.ncard) :
    ∃ t ⊆ s, t.Finite ∧ t.ncard = k := by
  obtain ⟨t, -, hts, rfl⟩ := exists_subsuperset_card_eq s.empty_subset (by simp) hks
  exact ⟨t, hts, hs.subset hts, rfl⟩

variable (α) in
/--
@isnad1 id=ex.0h2v.s4.f4444a4d921b from=translated src=- shape=686d814e vocab=9bfd4179
-/
lemma exists_ncard_eq [Infinite α] (k : ℕ) : ∃ s : Set α, s.Finite ∧ s.ncard = k := by
  simpa using exists_superset_ncard_eq finite_empty

end Set
