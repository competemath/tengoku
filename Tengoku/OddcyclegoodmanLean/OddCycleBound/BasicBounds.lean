import Tengoku.OddcyclegoodmanLean.OddCycleBound.Necklace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=le.1h4v.s5.5d8b97817eb0 from=translated src=- shape=a11b8773 vocab=68bbf54a
-/
theorem trace_compPow_nonneg (hW : IsGraphon W μ) (n : Nat) :
    0 <= trace μ (compPow μ W n) := by
  rw [trace]
  exact integral_nonneg fun x => compPow_nonneg hW n x x

end OddCycleBound
