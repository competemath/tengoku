import Tengoku.Piirrationalitymeasure.Formalization.ConstructionPrimeSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Floor form of the general saving condition. -/

namespace PiIrrationality

theorem constructionSavingCondition_floor (a b c : ℕ) (u : ℝ) :
    constructionSavingCondition a b c u ↔
      ((a : ℝ) + 2 * b - c) * u + 1 / 2 <
        (⌊(a : ℝ) * u + 1 / 2⌋ : ℝ) +
          2 * (⌊(b : ℝ) * u⌋ : ℝ) - (⌊(c : ℝ) * u⌋ : ℝ) := by
  unfold constructionSavingCondition
  simp only [Int.fract]
  have hq : ((a : ℝ) + 2 * b - c) * u + 1 / 2 =
      (a : ℝ) * u + 1 / 2 + 2 * ((b : ℝ) * u) - (c : ℝ) * u := by
    push_cast
    ring
  rw [hq]
  constructor <;> intro h <;> linarith

theorem constructionSavingCondition_floor_eq (a b c : ℕ) (u : ℝ) :
    constructionSavingCondition a b c u ↔
      ((a : ℝ) + 2 * b - c) * u + 1 / 2 <
        ((⌊(a : ℝ) * u + 1 / 2⌋ +
          2 * ⌊(b : ℝ) * u⌋ - ⌊(c : ℝ) * u⌋ : ℤ) : ℝ) := by
  rw [constructionSavingCondition_floor]
  congr 2
  push_cast
  ring

end PiIrrationality
