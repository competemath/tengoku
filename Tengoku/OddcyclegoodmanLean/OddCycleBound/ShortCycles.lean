import Tengoku.OddcyclegoodmanLean.OddCycleBound.ShortCycles.ExcursionPolynomials
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.ExpansionAssembly
import Tengoku.OddcyclegoodmanLean.OddCycleBound.BasicBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cycles `C_3`, `C_5`, `C_7` (Section 4)

For `m ∈ {3, 5, 7}` every excursion polynomial `P_{m,r}(q; ·)` is pointwise nonnegative when
`q = 1 - p ≤ 1/2` (Proposition 4.1, `multiKernel_nonneg_short`). Lemma 3.3 then gives
Theorem 1.3 and Theorem 1.1 for these cycles throughout `p ≥ 1/2`. For `p ≤ 1/2` the bound of
Theorem 1.1 is trivial.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/--
@isnad1 id=and.1h1v.s5.0ca9a3dc8ace from=translated src=- shape=b973a148 vocab=28094244
-/
lemma odd_of_short {m : ℕ} (hm : m = 3 ∨ m = 5 ∨ m = 7) : Odd m ∧ 3 ≤ m := by
  rcases hm with rfl | rfl | rfl
  exacts [⟨⟨1, rfl⟩, le_rfl⟩, ⟨⟨2, rfl⟩, by norm_num⟩, ⟨⟨3, rfl⟩, by norm_num⟩]

end OddCycleBound
