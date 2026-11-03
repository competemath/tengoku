import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Sigma
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Summing a single contributing shift in a supported family -/
set_option autoImplicit false
open scoped BigOperators
namespace MagnitudeConjecture
universe u v

/-- If a prescribed shift belongs to every fiber, summing a weight supported
at that shift retains one copy of each label's weight.
@isnad1 id=eq.1h5v.s8.50994ac67392 from=translated src=- shape=f8a457f6 vocab=6c24355d
-/
theorem sum_supported_single_shift {ι : Type u} [Fintype ι] {α : Type v}
    [DecidableEq α] (F : ι → Finset α) (s : α) (hs : ∀ i, s ∈ F i)
    (w : ι → ℕ) :
    (∑ a : (i : ι) × ↥(F i), if a.2.val = s then w a.1 else 0) = ∑ i, w i := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (⟨s, hs i⟩ : ↥(F i))]
  · simp
  · intro b _ hb
    have hbs : b.val ≠ s := fun h ↦ hb (Subtype.ext h)
    simp [hbs]
  · simp

/-- Apply the single-shift sum to any pointwise identified weight.
@isnad1 id=eq.2h6v.s8.3eacdce4b32e from=translated src=- shape=d4900761 vocab=6c24355d
-/
theorem sum_eq_of_supported_single_shift {ι : Type u} [Fintype ι] {α : Type v}
    [DecidableEq α] (F : ι → Finset α) (s : α) (hs : ∀ i, s ∈ F i)
    (w : ι → ℕ) (f : ((i : ι) × ↥(F i)) → ℕ)
    (hf : ∀ a, f a = if a.2.val = s then w a.1 else 0) :
    (∑ a, f a) = ∑ i, w i :=
  (Finset.sum_congr rfl (fun a _ ↦ hf a)).trans
    (sum_supported_single_shift F s hs w)

end MagnitudeConjecture
