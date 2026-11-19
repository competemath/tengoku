/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.ValueDecomposition
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.FiberDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Double decomposition of the local X-ray mixed norm

First split by transform size, then by the sizes of parallel fibers.
Both indices are natural numbers. A common finite fiber bound supplies
the initial scale for the second decomposition.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

/--
@isnad1 id=le.8h6v.s10.52adc9db24eb from=translated src=- shape=9a546ba8 vocab=3a670fb1
-/
theorem mixedNorm_localXRay_le_double_sum {m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hE : MeasurableSet E)
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : MeasurableSet Ξ) {B : ℝ} (hB : 0 < B)
    (hupper : ∀ (j : ℕ) (ξ : EuclideanSpace ℝ (Fin m)),
      volume ((fun x ↦ (x, ξ)) ⁻¹' richLines E Ξ ((1 / 2 : ℝ) ^ j / 2)) ≤ ENNReal.ofReal B)
    {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1))
        q r volume volume ≤ ∑' j : ℕ, ∑' l : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
          mixedNorm ((fiberBlock (richLines E Ξ ((1 / 2 : ℝ) ^ j / 2))
            (B * (1 / 2 : ℝ) ^ l)).indicator (fun _ ↦ (1 : ℝ≥0∞))) q r volume volume := by
  apply (mixedNorm_localXRay_le_tsum_richLines hE hΞ hq hr hqfin hrfin).trans
  apply ENNReal.tsum_le_tsum
  intro j
  rw [ENNReal.tsum_mul_left]
  apply mul_le_mul_right
  exact mixedNorm_indicator_le_tsum_fiberBlock (measurableSet_richLines hE hΞ _) hB
    (hupper j) hq hr hqfin hrfin

end NKBesicovitch.XRay
