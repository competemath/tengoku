import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Geometry
import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The geometric Brascamp–Lieb statement

`IntegralInequality` names the statement. Its proof is supplied by
`Datum.integralInequality` in `MeasurableInequality.lean`.
The extended nonnegative integral formulation includes infinite integrals and
zero weights without imposing additional integrability assumptions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]

/-- Geometric Brascamp–Lieb with sharp constant one for arbitrary nonnegative
measurable functions. See `Datum.integralInequality` for the proof.-/
def IntegralInequality (D : Datum ι E F) : Prop :=
  ∀ f : ∀ i, F i → ℝ≥0∞, (∀ i, Measurable (f i)) →
    (∫⁻ x, ∏ i, (f i (D.map i x)) ^ D.weight i) ≤
      ∏ i, (∫⁻ y, f i y) ^ D.weight i

end GeometricBrascampLieb.Datum
