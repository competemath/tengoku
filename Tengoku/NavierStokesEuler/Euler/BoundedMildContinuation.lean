import Tengoku.NavierStokesEuler.Euler.QuadraticMildPasting

/-! Genuine finite-time continuation of actual viscous mild solutions from an a priori Sobolev bound. -/

noncomputable section

namespace EulerBoundedMildContinuation

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
  EulerUniformHeatLocal EulerQuadraticSource EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology

/-- The next actual time window ends at the smaller of one full step and the terminal time. -/
theorem advance_time_eq (a δ S : ℝ) : a+min δ (S-a) = min (a+δ) S := by
  by_cases h : δ ≤ S-a
  · rw [min_eq_left h, min_eq_left (by linarith : a+δ ≤ S)]
  · rw [min_eq_right (le_of_not_ge h), min_eq_right (by linarith : S ≤ a+δ)]
    ring

/-- Repeated genuine local windows reach each successive point of a fixed finite time grid. -/
theorem advance_grid (S δ a : ℝ) (hδ : 0 ≤ δ) (n : ℕ)
    (hgrid : min ((n : ℝ)*δ) S ≤ a) :
    min (((n+1 : ℕ) : ℝ)*δ) S ≤ a+min δ (S-a) := by
  rw [advance_time_eq]
  apply le_min
  · by_cases hn : (n : ℝ)*δ ≤ S
    · have hna : (n : ℝ)*δ ≤ a := by simpa only [min_eq_left hn] using hgrid
      apply (min_le_left _ _).trans
      push_cast
      nlinarith only [hna]
    · have hSa : S ≤ a := by simpa only [min_eq_right (le_of_not_ge hn)] using hgrid
      exact (min_le_right _ _).trans (by linarith)
  · exact min_le_right _ _

variable (period : ℝ) [Fact (0 < period)]

end EulerBoundedMildContinuation
