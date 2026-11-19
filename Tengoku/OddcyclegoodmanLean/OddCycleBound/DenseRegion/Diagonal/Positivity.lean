import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.KernelForm
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.ExpansionAssembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

abbrev DiagKernelPosEll : Prop :=
  ∀ {m r t : ℕ}, 1 ≤ r → m - 2 * r = 2 * t + 1 → ∀ {q ℓ : ℝ},
    0 ≤ q → q ≤ 1 / 3 → 0 < ℓ → 0 ≤ diagKernel m r q ℓ

theorem diagKernel_nonneg_uniform (hpos : DiagKernelPosEll)
    {m r : ℕ} (hm : Odd m) (hr : 1 ≤ r) (hres : 2 * r < m) {q ℓ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (_hℓ : ℓ ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ diagKernel m r q ℓ := by
  obtain ⟨t, ht⟩ : ∃ t, m - 2 * r = 2 * t + 1 := by
    rcases hm with ⟨k, hk⟩; exact ⟨k - r, by omega⟩
  by_cases hn2r : 2 * t + 1 ≤ 2 * r
  · exact diagKernel_nonneg_two_r_ge (by omega) ht hn2r q ℓ
  · by_cases hℓ0 : ℓ ≤ 0
    · exact diagKernel_nonneg_le_zero (by omega) ht q ℓ (by linarith) hℓ0
    · exact hpos hr ht hq0 hq (not_le.mp hℓ0)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

end OddCycleBound.DenseRegion
