import Tengoku.SingularityCompleteLean.Singularity.L2InvariantMean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The nonamenability criterion for the right Markov operator

Amenability is expressed here by the classical existence of a nonnegative,
normalized, finitely additive invariant probability on every subset of the group.
Inversion identifies left and right invariant means. Absence of such a mean
therefore implies the spectral gap for the actual right Markov operator, under
positive finite support and semigroup generation. No laziness or symmetry is
required. Nonamenability of the relevant Fuchsian subgroups is a separate input.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Singularity

/-- The classical set-function definition of an invariant mean on a discrete group.-/
def HasInvariantMean (Γ : Type*) [Group Γ] : Prop :=
  ∃ m : Set Γ → ℝ, (∀ A, 0 ≤ m A) ∧ m ∅ = 0 ∧ m univ = 1 ∧
    (∀ A B, Disjoint A B → m (A ∪ B) = m A + m B) ∧
    ∀ g : Γ, ∀ A, m ((fun x => g * x) '' A) = m A

/-- Inversion identifies the left and right versions of invariant means.
@isnad1 id=iff.0h1v.s3.6b24245122df from=translated src=- shape=aa7e0af4 vocab=e7ff43ab
-/
theorem hasInvariantMean_iff_right (Γ : Type*) [Group Γ] :
    HasInvariantMean Γ ↔ HasRightInvariantMean Γ := by
  have hdisj (A B : Set Γ) (hAB : Disjoint A B) : Disjoint (Inv.inv '' A) (Inv.inv '' B) :=
    hAB.image (inv_injective.injOn (s := Set.univ)) (Set.subset_univ A) (Set.subset_univ B)
  constructor
  · rintro ⟨m, hpos, hemp, huniv, hadd, hinv⟩
    refine ⟨fun A => m (Inv.inv '' A), fun A => hpos _, ?_, ?_, ?_, ?_⟩
    · simpa only [image_empty] using hemp
    · simpa only [Set.image_univ_of_surjective inv_surjective] using huniv
    · intro A B hAB
      dsimp only
      rw [image_union]
      exact hadd _ _ (hdisj A B hAB)
    · intro g A
      have he : Inv.inv '' ((fun x => x * g) '' A) =
          (fun x => g⁻¹ * x) '' (Inv.inv '' A) := by
        rw [image_image, image_image]
        congr 1
        funext x
        exact mul_inv_rev x g
      dsimp only
      rw [he]
      exact hinv g⁻¹ _
  · rintro ⟨m, hpos, hemp, huniv, hadd, hinv⟩
    refine ⟨fun A => m (Inv.inv '' A), fun A => hpos _, ?_, ?_, ?_, ?_⟩
    · simpa only [image_empty] using hemp
    · simpa only [Set.image_univ_of_surjective inv_surjective] using huniv
    · intro A B hAB
      dsimp only
      rw [image_union]
      exact hadd _ _ (hdisj A B hAB)
    · intro g A
      have he : Inv.inv '' ((fun x => g * x) '' A) =
          (fun x => x * g⁻¹) '' (Inv.inv '' A) := by
        rw [image_image, image_image]
        congr 1
        funext x
        exact mul_inv_rev g x
      dsimp only
      rw [he]
      exact hinv g⁻¹ _

end Singularity
