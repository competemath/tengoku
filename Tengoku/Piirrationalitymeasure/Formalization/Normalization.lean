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

theorem normalizationCost_explicit (omega : ℝ) :
    normalizationCost omega =
      (7430 - 4645 * Real.log 2 - omega) / 5570 := by
  norm_num [normalizationCost, d0, h, c, a, b]

theorem normalizationCost_denominator_pos : 0 < (c : ℝ) := by
  norm_num [c]

theorem normalizationCost_strictAnti (omega₁ omega₂ : ℝ) (hω : omega₁ < omega₂) :
    normalizationCost omega₂ < normalizationCost omega₁ := by
  rw [normalizationCost_explicit, normalizationCost_explicit]
  have hc : (0 : ℝ) < 5570 := by norm_num
  apply (div_lt_div_iff_of_pos_right hc).2
  linarith

theorem normalizationCost_difference (omega₁ omega₂ : ℝ) :
    normalizationCost omega₁ - normalizationCost omega₂ =
      (omega₂ - omega₁) / 5570 := by
  rw [normalizationCost_explicit, normalizationCost_explicit]
  ring

end PiIrrationality
