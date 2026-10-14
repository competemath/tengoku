/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Product-box power integrals and their spatial slices

This module records the product-box form of the slice decomposition of a power
integral.  For a nonnegative function on `Vec3 × ℝ` and arbitrary sets `E` of
space points and `F` of times, the integral of the power `|g| ^ P` over the box
`E ×ˢ F` equals the integral over `F` of the spatial power integrals of the
slices `y ↦ g (y, s)`.

The second result turns an almost-everywhere bound on the `L^P` norm of the
spatial slices into a bound on the power integral over the whole box.  Both are
stated for an arbitrary spatial set and an arbitrary time set; no geometry of a
ball or a backward time window is used.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The power integral over a product box is the time integral of its spatial
slices.  No positivity hypothesis is needed on the exponent `P`.
@isnad1 id=eq.1h4v.s8.717cc9e106d4 from=translated src=- shape=3cd677c7 vocab=c6bb6982
-/
theorem prodPowerIntegral_eq_lintegral_slices
    {P : ℝ} {g : ParabolicPoint → ℝ} {E : Set Vec3} {F : Set ℝ}
    (hmeas : AEMeasurable g (volume.restrict (E ×ˢ F))) :
    (∫⁻ w in E ×ˢ F, ENNReal.ofReal |g w| ^ P) =
      ∫⁻ s in F, ∫⁻ y in E, ENNReal.ofReal |g (y, s)| ^ P := by
  have hprod : (volume.restrict (E ×ˢ F)) =
      (volume.restrict E).prod (volume.restrict F) := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
  have hmeas' : AEMeasurable g ((volume.restrict E).prod (volume.restrict F)) := by
    rw [← hprod]
    exact hmeas
  have hFm : AEMeasurable (fun w : ParabolicPoint => ENNReal.ofReal |g w| ^ P)
      ((volume.restrict E).prod (volume.restrict F)) := by
    have h1 : AEMeasurable (fun w : ParabolicPoint => ‖g w‖ₑ ^ P)
        ((volume.restrict E).prod (volume.restrict F)) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmeas'.enorm
    simpa only [Real.enorm_eq_ofReal_abs] using h1
  exact CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl hFm

end CKN.Core.Step4
