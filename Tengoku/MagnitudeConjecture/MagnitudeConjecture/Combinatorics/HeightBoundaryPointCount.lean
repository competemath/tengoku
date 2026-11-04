import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.HeightBoundaryBalance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Boundary sums with one exceptional vertex -/
set_option autoImplicit false
namespace MagnitudeConjecture.HeightArrowCount
universe u
variable {V : Type u} [Fintype V]

/-- Boundary degrees are one except at a single distinguished vertex.
@isnad1 id=and.1h4v.s6.96b14d0a38d1 from=translated src=- shape=7579e97a vocab=47201b9b
-/
theorem boundary_sums [DecidableEq V] (s : V) (h d : V → ℤ)
    (hd : ∀ x, d x = if x = s then 0 else 1) :
    (∑ x, d x) = Fintype.card V - 1 ∧
    (∑ x, h x * d x) = (∑ x, h x) - h s := by
  classical
  have he : ∀ x, d x = 1 - if x = s then 1 else 0 := by
    intro x
    rw [hd x]
    split_ifs <;> norm_num
  constructor
  · simp [he, Finset.sum_sub_distrib]
  · simp [he, mul_sub, Finset.sum_sub_distrib]

/-- Complementary translation sets have equally many boundary vertices.
@isnad1 id=eq.0h4v.s6.b30eacca42c4 from=translated src=- shape=bb856b6b vocab=bc4cbaee
-/
theorem boundary_card_eq (P I : V → Prop) [DecidablePred P] [DecidablePred I]
    (e : {x // ¬ P x} ≃ {x // ¬ I x}) :
    Fintype.card {x // P x} = Fintype.card {x // I x} := by
  have hp := Fintype.sum_subtype_add_sum_subtype P (fun _ : V ↦ (1 : ℤ))
  have hi := Fintype.sum_subtype_add_sum_subtype I (fun _ : V ↦ (1 : ℤ))
  have he : (Fintype.card {x // ¬ P x} : ℤ) = Fintype.card {x // ¬ I x} := by
    exact_mod_cast Fintype.card_congr e
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hp hi
  omega

end MagnitudeConjecture.HeightArrowCount
