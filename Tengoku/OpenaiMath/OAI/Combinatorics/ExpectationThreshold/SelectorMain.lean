import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCost
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorAverageColor
import Tengoku

namespace OAI

/-!
# The simultaneous multiscale selector

The actual minimum-move cover bounds the bad probability from below by its
weighted cost. The profile reconstruction and counting theorem bounds that
same cost from above. Both conclusions use the literal independent color law.
-/

noncomputable section
open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual selected changed sets give the cover-cost inequality. -/
theorem half_bad_probability_le_selected_cost {F : Family α}
    (mu : MassFamily F) (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (hF : ¬ Small p F) :
    (1 / 2 : ℝ) * (coloringLaw (α := α) p s hp hs).prob (Bad mu) ≤
      ∑ a : Coloring α s, if Bad mu a then
        colorMass p s a * ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card
      else 0 := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : Bad mu a
  · simp only [ite_eq_left ha, coloringLaw_weight]
    have hcover := (half_lt_selectedMoves_cost mu a hp.le hF).le
    have hmass := colorMass_nonneg p s hp hs a
    nlinarith
  · simp only [ite_eq_right ha, mul_zero, le_refl]

end TalagrandThreshold.Selector

end

end OAI
