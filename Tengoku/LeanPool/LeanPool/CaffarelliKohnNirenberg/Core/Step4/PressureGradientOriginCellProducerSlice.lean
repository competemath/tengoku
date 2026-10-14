/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Slice decomposition of the power integral on a parabolic cylinder

The power integral over a backward parabolic cylinder is the time integral of
the power integrals of its spatial slices.  Consequently a bound on the `L^P`
norm of almost every spatial slice controls the full cylinder power integral.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
noncomputable section
namespace CKN.Core.Step4

/-- The power integral of a parabolic cylinder is the time integral of its
spatial slices.
@isnad1 id=eq.2h5v.s7.2d47322e55c1 from=translated src=- shape=2d9ca017 vocab=ac79a2af
-/
theorem cylinderPowerIntegral_eq_lintegral_slices
    {P : ℝ} (hP : 0 < P) {g : ParabolicPoint → ℝ} {x : Vec3} {t r : ℝ}
    (hmeas : AEMeasurable g (volume.restrict (parabolicCylinder x t r))) :
    cylinderPowerIntegral P g (x, t) r =
      ∫⁻ s in Set.Ioc (t - r ^ 2) t,
        ∫⁻ y in vec3Ball x r, ENNReal.ofReal |g (y, s)| ^ P := by
  have _ : 0 < P := hP
  have hprod : (volume.restrict (vec3Ball x r ×ˢ Set.Ioc (t - r ^ 2) t)) =
      (volume.restrict (vec3Ball x r)).prod
        (volume.restrict (Set.Ioc (t - r ^ 2) t)) := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
  have hmeas' : AEMeasurable g ((volume.restrict (vec3Ball x r)).prod
      (volume.restrict (Set.Ioc (t - r ^ 2) t))) := by
    rw [← hprod]
    exact hmeas
  have hF : AEMeasurable (fun w : ParabolicPoint => ENNReal.ofReal |g w| ^ P)
      ((volume.restrict (vec3Ball x r)).prod
        (volume.restrict (Set.Ioc (t - r ^ 2) t))) := by
    have h1 : AEMeasurable (fun w : ParabolicPoint => ‖g w‖ₑ ^ P)
        ((volume.restrict (vec3Ball x r)).prod
          (volume.restrict (Set.Ioc (t - r ^ 2) t))) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmeas'.enorm
    simpa only [Real.enorm_eq_ofReal_abs] using h1
  unfold cylinderPowerIntegral
  exact CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl hF

end CKN.Core.Step4
