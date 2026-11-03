import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Defs
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Incoming sums are invariant under finite relabelling -/
set_option autoImplicit false
open scoped BigOperators
namespace MagnitudeConjecture
universe u v

/-- Transport a uniform incoming-weight bound through a bijection of labels.
@isnad1 id=le.2h7v.s6.e0aae86775b2 from=translated src=- shape=57a9fbe3 vocab=82e8aba9
-/
theorem incoming_sum_le_of_equiv {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → α → ℕ) (g : β → β → ℕ)
    (h : ∀ a b, f a b = g (e a) (e b)) (B : ℕ)
    (hB : ∀ b, (∑ a, g a b) ≤ B) (b : α) : (∑ a, f a b) ≤ B := by
  calc
    (∑ a, f a b) = ∑ a, g (e a) (e b) := Finset.sum_congr rfl (fun a _ ↦ h a b)
    _ = ∑ a, g a (e b) := e.sum_comp (fun a ↦ g a (e b))
    _ ≤ B := hB (e b)

end MagnitudeConjecture
