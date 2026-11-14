import Tengoku.Piirrationalitymeasure.Formalization.CoefficientLocalLimit
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual diagonal coefficient asymptotic (4.10). -/

namespace PiIrrationality

open Filter Asymptotics PowerSeries
open scoped Topology

theorem sqrt_scaled_asymptotic {p : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (h : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * p n) atTop
      (𝓝 (1 / Real.sqrt C))) :
    p ~[atTop] (fun n : ℕ => 1 / Real.sqrt (C * n)) := by
  apply isEquivalent_of_tendsto_one
  have hs : Real.sqrt C ≠ 0 := (Real.sqrt_pos.mpr hC).ne'
  convert! h.mul_const (Real.sqrt C) using 1
  · ext n
    simp only [Pi.div_apply, one_div, div_inv_eq_mul, Real.sqrt_mul hC.le]
    ring
  · simp [hs]

end PiIrrationality
