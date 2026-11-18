import Tengoku.Seed.SetTheory.Cardinal.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Fintype

/--
Rewrite a finite sum with an `if` condition as a sum over the subtype where the
condition holds
@isnad1 id=eq.0h4v.s6.eed29458ed04 from=translated src=- shape=896b2854 vocab=a8a8e9d1
-/
lemma sum_dite_eq_sum_subtype
    {α : Type*} [Fintype α]
    {β : Type*} [AddCommMonoid β]
    (P : α → Prop) [DecidablePred P]
    (f : (a : α) → P a → β) :
    (∑ a : α, if h : P a then f a h else 0)
      =
    ∑ a : {a : α // P a}, f a.1 a.2 := by
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ ↦ a.val) ?_ ?_ ?_ ?_
  · intro a _ _
    exact Finset.mem_univ _
  · intro a₁ _ _ a₂ _ _ h
    exact Subtype.ext h
  · intro b _ hb
    split_ifs at hb with h
    · exact ⟨⟨b, h⟩, Finset.mem_univ _, hb, rfl⟩
    · exact False.elim (hb rfl)
  · intro a _ _
    exact (dite_eq_left a.prop).symm

end Fintype

namespace One
/--
A finite type with a `1` element has nonzero cardinality.
@isnad1 id=ne.0h1v.s4.608be5710267 from=translated src=- shape=21777def vocab=c20c28c7
-/
lemma natCard_ne_zero_of_finite
    (H : Type*) [One H] [Finite H] :
    Nat.card H ≠ 0 := by
  exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩

/--
In characteristic zero, the cardinality of a finite type with a `1` element
is nonzero in any semiring.
@isnad1 id=ne.0h2v.s5.522e35399dc5 from=translated src=- shape=0fe5943a vocab=2fc190d4
-/
lemma natCast_natCard_ne_zero_of_finite
    (H : Type*) [One H] [Finite H]
    (k : Type*) [Semiring k] [CharZero k] :
    (Nat.card H : k) ≠ 0 := by
  intro h
  exact One.natCard_ne_zero_of_finite H (Nat.cast_eq_zero.mp h)

end One
