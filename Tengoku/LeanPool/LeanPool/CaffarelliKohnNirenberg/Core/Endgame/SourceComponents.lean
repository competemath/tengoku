/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-! # Component bounds for Euclidean vector-source Morrey norms

The Euclidean norm is bounded by the sum of the three absolute coordinate
values. The scalar triangle inequality transfers this comparison to the
Morrey norm without changing either exponent.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- The scalar Morrey triangle inequality for any integrability exponent at
least one. No restriction on the outer exponent is needed. -/
theorem morrey_norm_add_le {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z + g z) ≤ morreyNorm P τ f + morreyNorm P τ g := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr hP0).ne'
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  let μ := volume.restrict (parabolicCylinder z.1 z.2 r.1)
  have hfμ : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.restrict
  have hgμ : AEStronglyMeasurable g μ := hg.aestronglyMeasurable.restrict
  have hsum := eLpNorm_add_le (μ := μ) (f := f) (g := g) (p := ENNReal.ofReal P)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hPne ENNReal.ofReal_ne_top (hfμ.add hgμ),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hPne ENNReal.ofReal_ne_top hfμ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hPne ENNReal.ofReal_ne_top hgμ] at hsum
  have hsum' : cylinderPowerIntegral P (fun w => f w + g w) z r.1 ^ (1 / P) ≤
      cylinderPowerIntegral P f z r.1 ^ (1 / P) +
        cylinderPowerIntegral P g z r.1 ^ (1 / P) := by
    simpa only [ENNReal.toReal_ofReal hP0.le, Real.enorm_eq_ofReal_abs,
      Pi.add_apply, one_div, μ, cylinderPowerIntegral] using hsum
  have hcell : morreyCell P τ (fun w => f w + g w) z r.1 ≤
      morreyCell P τ f z r.1 + morreyCell P τ g z r.1 := by
    unfold morreyCell
    rw [← mul_add]
    exact mul_le_mul_right hsum' _
  exact hcell.trans (add_le_add
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell P τ f z s.1) r))
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell P τ g z s.1) r)))

end CKN.Core.Endgame
