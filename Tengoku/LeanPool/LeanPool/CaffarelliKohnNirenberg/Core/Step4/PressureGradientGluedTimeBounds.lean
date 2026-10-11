/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseField
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice

/-!
# Time integrability on fixed pressure carriers

The `3/2` power of a spatial norm, integrated in time over a fixed local box,
is the space-time power integral on that box: Tonelli exchanges the two. The
finiteness that identity delivers is stable under a finite fixed coefficient
and under extending the time window by zero. The coefficients below are fixed
before the time integral; no shrinking-cell growth is asserted.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

namespace CKN.Core.Step4

/-- Finite fixed coefficients preserve the `3/2` time bound. -/
theorem glued_time_const_mul_power {J : Set ℝ} {K : ℝ → ℝ≥0∞}
    (hm : AEMeasurable K (volume.restrict J))
    (hp : (∫⁻ t in J, K t ^ (3 / 2 : ℝ)) < ⊤)
    (C : ℝ≥0∞) (hC : C < ⊤) :
    AEMeasurable (fun t => C * K t) (volume.restrict J) ∧
    (∫⁻ t in J, (C * K t) ^ (3/2 : ℝ)) < ⊤ := by
  refine ⟨aemeasurable_const.mul hm, ?_⟩
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3/2)]
  exact (lintegral_const_mul'' _ (hm.pow_const (3/2 : ℝ))).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne) hp)

/-- Zero extension in time gives precisely a global measurable majorant
with finite `3/2` time power integral. -/
theorem glued_time_indicator_power {J : Set ℝ} {K : ℝ → ℝ≥0∞}
    (hJ : MeasurableSet J) (hm : AEMeasurable K (volume.restrict J))
    (hp : (∫⁻ t in J, K t ^ (3 / 2 : ℝ)) < ⊤) :
    AEMeasurable (J.indicator K) volume ∧
    (∫⁻ t, J.indicator K t ^ (3/2 : ℝ)) < ⊤ := by
  refine ⟨(aemeasurable_indicator_iff hJ).mpr hm, ?_⟩
  have heq : (fun t => J.indicator K t ^ (3/2 : ℝ)) =
      J.indicator (fun t => K t ^ (3/2 : ℝ)) := by
    funext t
    by_cases ht : t ∈ J
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3/2)]
  rw [heq, lintegral_indicator hJ]
  exact hp

end CKN.Core.Step4
