import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.HeightArrowCount
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.HeightTranslationSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Direct arrow counts from boundary degrees and translation -/
set_option autoImplicit false
namespace MagnitudeConjecture.HeightArrowCount
universe u
variable {V : Type u} [Fintype V]

/-- Translation reindexes the incoming weighted sum off the projective
boundary into the outgoing weighted sum off the injective boundary.
@isnad1 id=eq.2h7v.s9.2779e4772030 from=translated src=- shape=89568c9c vocab=2351e33d
-/
theorem weighted_translation_sum
    (P I : V → Prop) [DecidablePred P] [DecidablePred I]
    (e : {x // ¬ P x} ≃ {x // ¬ I x})
    (h incoming outgoing : V → ℤ)
    (he : ∀ x, h x.1 = h (e x).1 + 2)
    (ha : ∀ x, incoming x.1 = outgoing (e x).1) :
    (∑ x : {x // ¬ P x}, h x.1 * incoming x.1) =
      (∑ x : {x // ¬ I x}, h x.1 * outgoing x.1) +
        2 * ∑ x : {x // ¬ I x}, outgoing x.1 := by
  calc
    _ = ∑ x : {x // ¬ P x}, (h (e x).1 + 2) * outgoing (e x).1 :=
      Finset.sum_congr rfl (fun x _ ↦ by rw [he x, ha x])
    _ = ∑ x : {x // ¬ I x}, (h x.1 + 2) * outgoing x.1 :=
      e.sum_comp (fun x ↦ (h x.1 + 2) * outgoing x.1)
    _ = _ := by simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- The complete weighted-height count, with boundary sums explicit.
@isnad1 id=and.7h9v.s9.b9c359260b5f from=translated src=- shape=587e0490 vocab=5bd915b0
-/
theorem count_of_boundary_sums
    (P I : V → Prop) [DecidablePred P] [DecidablePred I]
    (e : {x // ¬ P x} ≃ {x // ¬ I x})
    (h incoming outgoing : V → ℤ) (A L : ℤ)
    (he : ∀ x, h x.1 = h (e x).1 + 2)
    (ha : ∀ x, incoming x.1 = outgoing (e x).1)
    (hflux : A = (∑ x, h x * incoming x) - ∑ x, h x * outgoing x)
    (htotal : ∑ x, outgoing x = A)
    (hpin : (∑ x : {x // P x}, h x.1 * incoming x.1) =
      ∑ x : {x // P x}, h x.1)
    (hiout : (∑ x : {x // I x}, h x.1 * outgoing x.1) =
      (∑ x : {x // I x}, h x.1) - L)
    (hicount : (∑ x : {x // I x}, outgoing x.1) =
      (Fintype.card {x // P x} : ℤ) - 1) :
    A = 2 * Fintype.card V - L - 2 ∧
      2 * Fintype.card V - A - Fintype.card {x // P x} - 1 =
        L - ((Fintype.card {x // P x} : ℤ) - 1) := by
  have htr := weighted_translation_sum P I e h incoming outgoing he ha
  have hp := Fintype.sum_subtype_add_sum_subtype P (fun x ↦ h x * incoming x)
  have hi := Fintype.sum_subtype_add_sum_subtype I (fun x ↦ h x * outgoing x)
  have ho := Fintype.sum_subtype_add_sum_subtype I outgoing
  apply count_of_balance A (Fintype.card V) (Fintype.card {x // P x}) L
    (∑ x : {x // P x}, h x.1) (∑ x : {x // I x}, h x.1)
    (∑ x : {x // ¬ I x}, outgoing x.1)
  · exact boundary_height_difference P I e h he
  · omega
  · omega

end MagnitudeConjecture.HeightArrowCount
