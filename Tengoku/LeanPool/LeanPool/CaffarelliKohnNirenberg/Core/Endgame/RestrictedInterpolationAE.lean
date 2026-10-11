/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationRestricted
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.ENNRealHalfScale

/-! # Restricted interpolation with almost-everywhere sublinearity

This version of the restricted interpolation argument permits null exceptional
sets in sublinearity. The tail containment is interpreted modulo null sets;
the truncations, layer-cake argument, and numerical constant are unchanged
from `Foundation.Euclidean.InterpolationRestricted`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-! ### The layer-cake integration -/

/-- The layer-cake half of the interpolation theorem: the distribution-function
bound at every level, integrated against the weight `p t^{p-1}`.  This is the proof
of `interpolation_weak11_strong22` with the tail estimate taken as a hypothesis. -/
private lemma interpolation_of_tail_bound {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ p : ℝ}
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2) {f : Vec3 → ℝ} (hf : Measurable f)
    (hTf : Measurable (T f))
    (htail : ∀ t : ℝ, 0 < t → volume {x | t < |T f x|} ≤
      ENNReal.ofReal (2 * A₁ / t) * highTail (absE f) t +
        ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * lowTail (absE f) t) :
    ∫⁻ x, absE (T f) x ^ p ≤
      ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
        ∫⁻ x, absE f x ^ p := by
  exact _root_.CKN.Foundation.Euclidean.interpolation_of_tail_bound hA₁ hp1 hp2 hf hTf htail

end CKN.Core.Endgame
