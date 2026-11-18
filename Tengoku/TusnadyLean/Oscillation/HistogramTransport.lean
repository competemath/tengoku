import Tengoku.TusnadyLean.Oscillation.Histogram
import Tengoku.Seed.MeasureTheory.Constructions.Pi
import Tengoku.Seed.MeasureTheory.Integral.Bochner.SumMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact transport from iid points to their finite bucket labels. -/
namespace Oscillation
open scoped BigOperators
open MeasureTheory
noncomputable section

variable {α Ω : Type*} [MeasurableSpace α] [Fintype Ω] [DecidableEq Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The actual probability of a classification bucket.-/
def bucketProbability (μ : Measure α) (cell : α → Ω) (c : Ω) : ℝ :=
  (μ {x | cell x = c}).toReal

/-- Sum of square roots of the actual interior bucket counts in a sample.-/
def bucketSquareRootSum {n M : ℕ} (cell : α → Option (Fin M)) (P : Fin n → α) : ℝ :=
  ∑ c : Fin M, Real.sqrt ((Finset.univ.filter (fun i => cell (P i) = some c)).card)

omit [MeasurableSpace α] in
/--
@isnad1 id=eq.0h5v.s5.cdb9a5ed2bfb from=translated src=- shape=e377b193 vocab=a9796720
-/
lemma bucketSquareRootSum_eq {n M : ℕ} (cell : α → Option (Fin M)) (P : Fin n → α) :
    bucketSquareRootSum cell P = interiorSum (histogram (fun i => cell (P i))) := by
  simp only [bucketSquareRootSum, interiorSum, histogramCount_eq_card]

end
end Oscillation
