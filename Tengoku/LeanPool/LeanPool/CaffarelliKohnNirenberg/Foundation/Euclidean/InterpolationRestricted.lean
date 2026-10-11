/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Interpolation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationLpChar
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationTruncBounds
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationIndicator
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.ENNRealHalfScale

/-!
# Marcinkiewicz interpolation for operators defined on a restricted class

`interpolation_weak11_strong22` (`Interpolation.lean`) assumes sublinearity, the
weak `(1,1)` bound and the strong `(2,2)` bound for *every* measurable function.
A Calderón--Zygmund operator obtained as the `L^2`-extension of a singular
integral does not satisfy such hypotheses: outside `L^2` it is only defined by a
convention, so the endpoint estimates hold only on the classes on which the
operator is genuinely defined.

This file proves the same conclusion, with the same constant
`p · 2^p · (A₁/(p-1) + A₂²/(2-p))` for `1 < p < 2`, from hypotheses restricted to
the classes actually visited by the truncation argument.  Two variants are
provided:

* `interpolation_weak11_strong22_of_classes`, whose endpoint hypotheses are
  assumed for integrable functions (weak `(1,1)`) and for `L^2` functions
  (strong `(2,2)`), with sublinearity only for an (integrable, `L^2`) pair;
* `interpolation_weak11_strong22_of_l2_classes`, whose hypotheses are in
  addition confined to `L^2` inputs throughout, which is the form available for
  an operator constructed as an `L^2`-extension and only later extended to `L^p`
  by density.

Splitting `f` at the level `t/2` produces the two pieces `f·1_{|f| > t/2}` and
`f·1_{|f| ≤ t/2}`.  For `f ∈ L^p` with `1 < p < 2` the first is integrable and
the second lies in `L^2`; these two facts, proved here from the pointwise bounds
of `InterpolationTruncBounds.lean`, are what lets the restricted hypotheses be
applied.  Everything else is the argument of `Interpolation.lean`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-! ### The two truncations of an `L^p` function -/

/-! ### The distribution-function bound from the two pieces -/

/-! ### The layer-cake integration -/

/-- The layer-cake half of the interpolation theorem: the distribution-function
bound at every level, integrated against the weight `p t^{p-1}`.  This is the proof
of `interpolation_weak11_strong22` with the tail estimate taken as a hypothesis. -/
lemma interpolation_of_tail_bound {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ p : ℝ}
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2) {f : Vec3 → ℝ} (hf : Measurable f)
    (hTf : Measurable (T f))
    (htail : ∀ t : ℝ, 0 < t → volume {x | t < |T f x|} ≤
      ENNReal.ofReal (2 * A₁ / t) * highTail (absE f) t +
        ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * lowTail (absE f) t) :
    ∫⁻ x, absE (T f) x ^ p ≤
      ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
        ∫⁻ x, absE f x ^ p := by
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hM : Measurable (absE f) := measurable_absE hf
  have hMfin : ∀ x, absE f x < ∞ := fun _ => ENNReal.ofReal_lt_top
  let _ : SFinite (volume : Measure Vec3) := inferInstance
  have hF1 : AEMeasurable (fun t : ℝ => ENNReal.ofReal (2 * A₁) *
      (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_weightedHighIntegrand hM (p := p)).lintegral_prod_right.congr
      (Eventually.of_forall fun t => inner_High_eq hM t)).const_mul _
  calc ∫⁻ x, absE (T f) x ^ p
      = ∫⁻ t in Ioi (0 : ℝ), volume {x | t < |T f x|} * ENNReal.ofReal (p * t ^ (p - 1)) :=
        layer_cake hTf hp1
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A₁ / t) * highTail (absE f) t +
            ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * lowTail (absE f) t) *
          ENNReal.ofReal (p * t ^ (p - 1)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_le_mul_left (htail t ht) _
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A₁) *
              (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t) +
            ENNReal.ofReal (4 * A₂ ^ 2) *
              (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail (absE f) t)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [interp_integrand hA₁ hp1 ht, ← rpowExt_eq (a := p - 2) ht,
          ← rpowExt_eq (a := p - 3) ht]
    _ = ENNReal.ofReal p *
          ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * A₁) *
              (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t)) +
            (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (4 * A₂ ^ 2) *
              (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail (absE f) t))) := by
        rw [lintegral_add_left' hF1]
    _ = ENNReal.ofReal p *
          (ENNReal.ofReal (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p))) *
            ∫⁻ x, absE f x ^ p) := by
        rw [weighted_combined hM hMfin hA₁ hp1 hp2]
    _ = ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
          ∫⁻ x, absE f x ^ p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hp0]

/-! ### Interpolation with hypotheses restricted to the endpoint classes -/

/-! ### The exponents used by the pressure estimates -/

end CKN.Foundation.Euclidean
