/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedFar
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamel
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-!
# Source Morrey Data

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3

noncomputable section

namespace CKN.Core.Step4

/-! Product estimates used by the divergence-form sources.  The cutoff
factors are deliberately represented by their finite Morrey norms here; the
smooth compact-support cutoff API supplies those bounds at the point where a
cutoff is chosen. -/

theorem source_product_morrey_bound
    {P P₁ P₂ θ θ₁ θ₂ : ℝ}
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂)
    (hrelP : 1 / P = 1 / P₁ + 1 / P₂)
    (hrelθ : 1 / θ = 1 / θ₁ + 1 / θ₂)
    {f g : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (h₁ : morreyNorm P₁ θ₁ f < ∞)
    (h₂ : morreyNorm P₂ θ₂ g < ∞) :
    morreyNorm P θ (fun z => f z * g z) < ∞ ∧
      morreyNorm P θ (fun z => f z * g z) ≤
        morreyNorm P₁ θ₁ f * morreyNorm P₂ θ₂ g := by
  have hbound := morreyNorm_holder hP₁ hP₂ hrelP hrelθ hf hg
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top h₁ h₂), hbound⟩

/- The two heat-kernel families in the pointwise estimate are therefore
available directly from the source Morrey norms.  The Riesz families are
kept as separate fields in the consumer until the singular-source bridge is
established; this prevents silently replacing that bridge by an L¹ assertion. -/

end CKN.Core.Step4
