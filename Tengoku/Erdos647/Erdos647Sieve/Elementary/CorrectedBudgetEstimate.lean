/-
Combines the fixed-constant small-prime debit and the Stirling-derived residual.
The budget remains signed. There is no assumed asymptotic budget bound.
-/
import Tengoku.Erdos647.Erdos647Sieve.Elementary.LogBudgetFactorial
import Tengoku.Erdos647.Erdos647Sieve.Elementary.SmallPrimeDebitEstimate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped Topology
open Filter Real

noncomputable section
namespace Erdos647Sieve.Elementary

/-- An eventual upper estimate retaining all constants needed for the endpoint gap.-/
theorem correctedBudget_upper_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop,
      (Erdos647Sieve.correctedBudget H : ℝ) / (H : ℝ) ≤
        Real.log (H : ℝ) / Real.log 2 - Real.log (Real.log (H : ℝ)) +
          2 - 1 / Real.log 2 + ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun H : ℕ =>
      ((shiftedFactorialLog H -
        ((H : ℝ) * Real.log (H : ℝ) - (H : ℝ))) / (H : ℝ)) / Real.log 2)
      atTop (𝓝 0) := by
    simpa using shiftedFactorialLog_residual_tendsto_zero.div_const (Real.log 2)
  have hsmall : ∀ᶠ H : ℕ in atTop,
      ((shiftedFactorialLog H -
        ((H : ℝ) * Real.log (H : ℝ) - (H : ℝ))) / (H : ℝ)) / Real.log 2 < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall] with H hH hsmallH
  have hHR : 0 < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hQ := logBudget_le_factorial H
  have hD := smallPrimeDebit_lower H hH
  have hB : (Erdos647Sieve.correctedBudget H : ℝ) =
      (Erdos647Sieve.logBudget H : ℝ) - (Erdos647Sieve.smallPrimeDebit H : ℝ) := by
    simp only [Erdos647Sieve.correctedBudget, Int.cast_sub, Int.cast_natCast]
  have hb : (Erdos647Sieve.correctedBudget H : ℝ) ≤
      shiftedFactorialLog H / Real.log 2 -
        (H : ℝ) * (Real.log (Real.log (H : ℝ)) - 2) := by
    rw [hB]
    linarith
  calc
    (Erdos647Sieve.correctedBudget H : ℝ) / (H : ℝ)
        ≤ (shiftedFactorialLog H / Real.log 2 -
          (H : ℝ) * (Real.log (Real.log (H : ℝ)) - 2)) / (H : ℝ) :=
      div_le_div_of_nonneg_right hb hHR.le
    _ = Real.log (H : ℝ) / Real.log 2 - Real.log (Real.log (H : ℝ)) +
          2 - 1 / Real.log 2 +
          ((shiftedFactorialLog H -
            ((H : ℝ) * Real.log (H : ℝ) - (H : ℝ))) / (H : ℝ)) / Real.log 2 := by
      field_simp [hHR.ne', hl.ne']
      ring
    _ ≤ Real.log (H : ℝ) / Real.log 2 - Real.log (Real.log (H : ℝ)) +
          2 - 1 / Real.log 2 + ε := add_le_add le_rfl hsmallH.le

end Erdos647Sieve.Elementary
end
