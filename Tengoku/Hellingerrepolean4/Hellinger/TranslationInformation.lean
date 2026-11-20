import Tengoku.Hellingerrepolean4.Hellinger.EntropyTransfer
import Tengoku.Hellingerrepolean4.Hellinger.TranslationEquality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The information theorem and its full signed-dictator equality
classification for arbitrary nonempty sign-reversing coordinate sets. -/

set_option autoImplicit false
noncomputable section

namespace Hellinger.TranslationInformation

/--
@isnad1 id=translat.0h0v.s0.1879ec452686 from=translated src=- shape=45709ebd vocab=1879ec45
-/
theorem translation_information : PaperSpecs.TranslationInformation := by
  intro n f hf S hS hanti ρ hρ
  obtain ⟨hm, _, hH⟩ := ChannelSections.translation_hellinger n f hf S hS hanti ρ hρ
  refine ⟨EntropyTransfer.hellinger_implies_ck f hf ρ hρ hH, ?_⟩
  intro hρpos hρlt
  constructor
  · intro hI
    have hobj := EntropyTransfer.ck_equality_implies_hellinger_equality f hf ρ hρ hH hI
    unfold objective at hobj
    rw [UniformChannel.mean_apply, hm] at hobj
    have hz : root (0 : ℝ) = 1 := by norm_num [root]
    rw [hz] at hobj
    have hroot : PaperSpecs.posteriorRootMean f ρ hρ = root ρ := by
      unfold PaperSpecs.posteriorRootMean
      linarith
    exact (TranslationEquality.translation_equality n f hf S hS hanti ρ hρ hρpos hρlt).mp hroot
  · rintro ⟨i, _, negative, hform⟩
    rw [hform]
    exact EntropyTransfer.signed_dictator_information n i negative ρ hρ

end Hellinger.TranslationInformation
