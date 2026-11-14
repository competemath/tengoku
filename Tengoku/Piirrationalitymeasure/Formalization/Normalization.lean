import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.PiIrrationality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The normalized clearing-denominator cost from equation (3.27).
The prime-saving quantity is kept abstract here; arithmetic identities for the
selected parameter triple are proved in this module.
-/

namespace PiIrrationality

noncomputable def normalizationCost (omega : ℝ) : ℝ :=
  ((d0 : ℝ) - (h : ℝ) * Real.log 2 - omega) / (c : ℝ)

/--
@isnad1 id=eq.0h1v.s6.41ca6e5b940e from=translated src=- shape=3dce3dd7 vocab=053effec
-/
theorem normalizationCost_explicit (omega : ℝ) :
    normalizationCost omega =
      (7430 - 4645 * Real.log 2 - omega) / 5570 := by
  norm_num [normalizationCost, d0, h, c, a, b]

/--
@isnad1 id=lt.0h0v.s3.d29063d8965e from=translated src=- shape=62e5f382 vocab=a5035bc7
-/
theorem normalizationCost_denominator_pos : 0 < (c : ℝ) := by
  norm_num [c]

/--
@isnad1 id=lt.1h2v.s4.e95a25dc0954 from=translated src=- shape=c5a9c46f vocab=94fbc99c
-/
theorem normalizationCost_strictAnti (omega₁ omega₂ : ℝ) (hω : omega₁ < omega₂) :
    normalizationCost omega₂ < normalizationCost omega₁ := by
  rw [normalizationCost_explicit, normalizationCost_explicit]
  have hc : (0 : ℝ) < 5570 := by norm_num
  apply (div_lt_div_iff_of_pos_right hc).2
  linarith

/--
@isnad1 id=eq.0h2v.s5.8aae787f18cf from=translated src=- shape=8283fc84 vocab=b04f4fe3
-/
theorem normalizationCost_difference (omega₁ omega₂ : ℝ) :
    normalizationCost omega₁ - normalizationCost omega₂ =
      (omega₂ - omega₁) / 5570 := by
  rw [normalizationCost_explicit, normalizationCost_explicit]
  ring

end PiIrrationality
