import Tengoku.Piirrationalitymeasure.Formalization.ConstructionPrimeSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Floor form of the general saving condition. -/

namespace PiIrrationality

/--
@isnad1 id=iff.0h4v.s7.1cb785430bd3 from=translated src=- shape=e3b945c9 vocab=047f7239
-/
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

/--
@isnad1 id=iff.0h4v.s7.9620f3fb1aef from=translated src=- shape=9f150116 vocab=59422848
-/
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
