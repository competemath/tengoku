import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.RoundingMasses
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.RoundingLowerBound
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.RoundingProbabilityContradiction
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.ColorMean
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorMain

namespace OAI

/-!
# Actual rounding of an unrestricted fractional cover

The concrete member masses feed the proved multiscale selector. The same
independent color law supplies the lower and upper bounds on the subset-product
score. No selector hypothesis or bound on support sizes appears in the result.
-/

open scoped BigOperators

noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem fractionalCover_empty_not_mem {F : Family α} {g : Finset α → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hcover : FractionalCover F g) (hcost : fracCost r g ≤ 1 / 2) :
    (∅ : Finset α) ∉ F := by
  intro hempty
  have hcoverEmpty : (1 : ℝ) ≤ g ∅ := by
    simpa only [Finset.powerset_empty, Finset.sum_singleton] using hcover.2 ∅ hempty
  have hweight : g ∅ ≤ (1 / 2 : ℝ) :=
    (empty_weight_le_fracCost hr hcover.nonneg).trans hcost
  exact (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2)) (hcoverEmpty.trans hweight)

/-- The actual normalized probability masses attached to family members. -/
def fractionalMassFamily (F : Family α) (g : Finset α → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hcover : FractionalCover F g) (hcost : fracCost r g ≤ 1 / 2) :
    Selector.MassFamily F where
  weight H := roundingMass g H.val
  nonneg H x := roundingMass_nonneg g H.val hcover.nonneg
    (memberMass_pos_of_fractionalCover hcover H.property hr hcost) x
  total H := roundingMass_sum g H.val
    (memberMass_pos_of_fractionalCover hcover H.property hr hcost)
  supported H _ hx := roundingMass_eq_zero_of_not_mem g H.val hx

end TalagrandThreshold

end

end OAI
