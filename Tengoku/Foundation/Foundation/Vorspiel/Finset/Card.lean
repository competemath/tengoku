module

public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku.Seed.Algebra.Order.Ring.Nat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace Finset

variable {α} {s t : Finset α}

/--
@isnad1 id=lt.2h3v.s5.9ed34e35f552 from=translated src=- shape=715e4d9b vocab=99b0c4a2
-/
lemma ssubset_of_subset_lt_card
  (h_subset : s ⊆ t)
  (h_card_le : s.card < t.card) : s ⊂ t := by
  constructor;
  . assumption;
  . by_contra hC;
    have : t = s := Finset.eq_iff_card_le_of_subset hC |>.mp (by omega);
    subst this;
    simp at h_card_le;

lemma eq_card_of_eq (h : s = t) : s.card = t.card := by tauto;

/--
@isnad1 id=le.1h4v.s5.0744d70991d8 from=translated src=- shape=301c0e97 vocab=8b8c6ed5
-/
lemma sum_le_card
  {n} {f : α → ℕ}
  (hf : ∀ a ∈ s, f a ≤ n)
  : (∑ a ∈ s, f a) ≤ s.card * n :=
  calc
    _ ≤ (∑ x ∈ s, n) := by apply Finset.sum_le_sum hf
    _ = s.card * n   := by simp_all;

end Finset

end
