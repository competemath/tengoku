import Tengoku.Seed.MeasureTheory.Integral.CircleAverage
import Tengoku.Seed.MeasureTheory.Measure.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted integration of a nonnegative circle-kernel inequality

This is a measure-theoretic statement about arbitrary measurable nonnegative
extended functions. Its pointwise angular hypothesis can be supplied by a
local geometric argument; no plurisubharmonicity, real representative, local
integrability, or finiteness of either integral is assumed here.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Tonelli's theorem integrates a pointwise angular bound against an arbitrary
measurable nonnegative weight. The bound is needed only where the weight is
nonzero, and the coefficient and weight may both take the value infinity.
@isnad1 id=le.3h7v.s8.a1c7dedecb45 from=translated src=- shape=6d662f86 vocab=f66bb7ee
-/
theorem weighted_circle_lintegral_le_of_pointwise
    (μ : Measure E) [SFinite μ] {D w : E → ℝ≥0∞}
    (hD : Measurable D) (hw : Measurable w) (v : E) (r : ℝ) {κ : ℝ≥0∞}
    (hpoint : ∀ x ∈ Function.support w,
      (∫⁻ t in Ioc 0 (2 * Real.pi), D (x + circleMap 0 r t • v)) ≤ κ * D x) :
    (∫⁻ t in Ioc 0 (2 * Real.pi),
        ∫⁻ x, w x * D (x + circleMap 0 r t • v) ∂μ) ≤
      κ * ∫⁻ x, w x * D x ∂μ := by
  have hc : Continuous (fun p : E × ℝ => p.1 + circleMap 0 r p.2 • v) := by
    fun_prop
  have hm : Measurable (fun p : E × ℝ => w p.1 * D (p.1 + circleMap 0 r p.2 • v)) :=
    (hw.comp measurable_fst).mul (hD.comp hc.measurable)
  have hswap := lintegral_lintegral_swap (μ := μ)
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))
    (f := fun x t => w x * D (x + circleMap 0 r t • v)) hm.aemeasurable
  have hweighted (x : E) :
      (∫⁻ t in Ioc 0 (2 * Real.pi), w x * D (x + circleMap 0 r t • v)) ≤
        κ * (w x * D x) := by
    by_cases hx : w x = 0
    · simp [hx]
    have hmangle : Measurable (fun t : ℝ => D (x + circleMap 0 r t • v)) :=
      hD.comp (by fun_prop : Continuous (fun t : ℝ => x + circleMap 0 r t • v)).measurable
    rw [lintegral_const_mul (w x) hmangle]
    have hs := mul_le_mul_left (hpoint x hx) (w x)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  rw [← hswap]
  exact (lintegral_mono hweighted).trans_eq (lintegral_const_mul κ (hw.mul hD))

end PshLines
