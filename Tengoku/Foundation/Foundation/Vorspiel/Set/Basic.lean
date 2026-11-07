module

public import Tengoku.Seed.Data.Set.Countable
public import Tengoku.Seed.Tactic.TautoSet
public import Tengoku.Seed.Data.Set.Finite.Range
public import Tengoku.Seed.Order.Filter.Ultrafilter.Defs

namespace Set
end Set

namespace FoundationFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace Set
open _root_.Set

variable {α : Type*} {s t : Set α} {a b : α}

/--
@isnad1 id=iff.0h4v.s5.1b7253612f19 from=translated src=- shape=9ff12f51 vocab=331d50fe
-/
lemma doubleton_subset : ({a, b} : Set α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . intro h;
    have ⟨ha, hb⟩ := Set.insert_subset_iff.mp h;
    tauto;
  . rintro ⟨ha, hb⟩;
    apply Set.insert_subset_iff.mpr;
    constructor;
    . assumption;
    . simpa;

/--
@isnad1 id=iff.0h4v.s5.8748c76a7059 from=translated src=- shape=34855413 vocab=0f12c626
-/
lemma iff_subset_insert_subset_diff : s ⊆ insert a t ↔ s \ {a} ⊆ t := by
  constructor;
  . intro ha b hb;
    rcases ha hb.1 with (rfl | hb);
    . simp at hb;
    . assumption;
  . intro ha b hb;
    apply or_iff_not_imp_left.mpr
    intro h;
    apply ha;
    constructor;
    . assumption;
    . simpa;

/--
@isnad1 id=lt.2h3v.s5.9959d4aa762a from=translated src=- shape=065a5058 vocab=4f3b14bd
-/
lemma ssubset_of_subset_ne (h : s ⊆ t) (hne : s ≠ t) : s ⊂ t := by
  constructor;
  . assumption;
  . revert hne;
    contrapose!;
    intro _;
    apply Set.eq_of_subset_of_subset <;> assumption;

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539292838
-/
/--
@isnad1 id=ex.3h3v.s7.1039e62447ff from=translated src=- shape=c9d7c860 vocab=c92b3a25
-/
lemma infinitely_finset_approximate (count : s.Countable) (inf : s.Infinite) (ha : a ∈ s) :
  ∃ f : ℕ → Finset α, ((f 0) = {a}) ∧ (∀ i, f i ⊂ f (i + 1)) ∧ (∀ i, ↑(f i) ⊆ s) ∧ (∀ b ∈ s, ∃ i, b ∈ f i) := by
  let X' := s \ {a}
  have count' : Countable X' := (count.mono Set.sdiff_subset).to_subtype
  have inf' : Infinite X' := (inf.sdiff (Set.finite_singleton a)).to_subtype
  obtain ⟨eq⟩ : Nonempty (Nat ≃ X') := nonempty_equiv_of_countable
  refine ⟨
    fun n => Finset.cons a ((Finset.range n).map
    (eq.toEmbedding.trans (Function.Embedding.subtype _))) ?_, ?_, ?_, ?_, ?_
  ⟩
  · suffices ∀ x < n, ¬↑(eq x) = a by simpa;
    intro x _
    exact (eq x).prop.right
  · rfl
  · simp [Finset.ssubset_def]
  · suffices ∀ (i : ℕ), Set.Iio i ⊆ (fun a ↦ ↑(eq a)) ⁻¹' s by simpa [Set.insert_subset_iff, ha]
    intro i x _;
    exact (eq x).prop.left
  · intro b hb
    by_cases hba : b = a
    · exact ⟨0, by simp [hba]⟩
    · refine ⟨eq.symm ⟨b, hb, hba⟩ + 1, ?_⟩
      apply Finset.mem_cons_of_mem;
      suffices ∃ a_1 < eq.symm ⟨b, _⟩ + 1, ↑(eq _) = b by simpa;
      exact ⟨eq.symm ⟨b, hb, hba⟩, by simp⟩

/--
@isnad1 id=ex.4h3v.s6.9c3982adbacf from=translated src=- shape=17e57dd3 vocab=f0cec1b7
-/
lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain : IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on s hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by
          have : (∃ t ∈ c, a ∈ t) ∧ s ⊆ ⋃₀ c := by simpa [Set.insert_subset_iff] using h
          exact this.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

end Set

end
