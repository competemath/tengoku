import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Statement
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Continuity
import Tengoku.Seed.Topology.Order.MonotoneConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite products and real powers commute with increasing suprema -/

noncomputable section
open Filter
open scoped ENNReal Topology BigOperators

namespace GeometricBrascampLieb

theorem iSup_ennreal_rpow_of_monotone (u : ℕ → ℝ≥0∞) (hu : Monotone u)
    {c : ℝ} (hc : 0 ≤ c) :
    (⨆ n, (u n)^c) = (⨆ n, u n)^c :=
  iSup_eq_of_tendsto (fun _ _ h => ENNReal.rpow_le_rpow (hu h) hc)
    ((tendsto_atTop_iSup hu).ennrpow_const c)

/-- Increasing finite products commute with supremum even when zero and infinity coexist.-/
theorem prod_iSup_ennreal_of_monotone {ι : Type*} (s : Finset ι)
    (u : ι → ℕ → ℝ≥0∞) (hu : ∀ i, Monotone (u i)) :
    (∏ i ∈ s, ⨆ n, u i n) = ⨆ n, ∏ i ∈ s, u i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, ih, ENNReal.iSup_mul, ENNReal.mul_iSup]
    apply le_antisymm
    · apply iSup_le
      intro m
      apply iSup_le
      intro n
      apply le_iSup_of_le (max m n)
      exact mul_le_mul' (hu a (le_max_right m n))
        (Finset.prod_le_prod' fun i _ => hu i (le_max_left m n))
    · apply iSup_le
      intro n
      exact le_iSup_of_le n (le_iSup_of_le n le_rfl)

end GeometricBrascampLieb
