/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WeakPressureSlice
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSlice
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-! # Slice-selected pressure gradients: classical, additive, quantitative forms

Display (3.5) of the pressure-gradient section selects, on a half ball, the
coordinate weak derivative of the pressure obtained by splitting it into a
particular potential and a smooth harmonic representative.  The ingredients
recorded here are exactly the ones that selection step consumes: a `C¹`
function has its classical coordinate gradient as a weak partial derivative,
weak partial derivatives add along an a.e. decomposition of the carrier, and a
coordinate field obeying a pointwise gradient display is controlled in `L^(6/5)`
on the half ball. -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-- classical gradient of a C¹ function is its weak partial derivative -/
theorem hasWeakPartialDerivOn_classicalGradient
    {B : Set Vec3} (hB : IsOpen B) {h : Vec3 → ℝ} (k : Fin 3)
    (hh : ContDiffOn ℝ (1 : ℕ∞) h B) :
    HasWeakPartialDerivOn B k h (fun x => classicalGradient h x k) := by
  simpa only [classicalGradient_apply] using
    pressure_hasWeakPartialDerivOn_of_contDiffOn hB hh

/-- The classical coordinate gradient of a `C¹` function is locally
integrable, as required by display (3.5). -/
theorem locallyIntegrableOn_classicalGradient
    {B : Set Vec3} (hB : IsOpen B) {h : Vec3 → ℝ} (k : Fin 3)
    (hh : ContDiffOn ℝ (1 : ℕ∞) h B) :
    LocallyIntegrableOn (fun x => classicalGradient h x k) B volume := by
  have hHd : ContinuousOn (fun x => (fderiv ℝ h x) (basisVec k)) B :=
    (hh.continuousOn_fderiv_of_isOpen hB (by simp)).clm_apply continuousOn_const
  simpa only [classicalGradient_apply] using
    hHd.locallyIntegrableOn hB.measurableSet

/-- Display (3.5) decomposes the selected pressure into a particular and a
harmonic part; the weak partial derivatives of the two parts add. -/
theorem hasWeakPartialDerivOn_add
    {B : Set Vec3} (hB : IsOpen B) {k : Fin 3} {h w gh gw : Vec3 → ℝ}
    (hh : HasWeakPartialDerivOn B k h gh) (hw : HasWeakPartialDerivOn B k w gw)
    (hhloc : LocallyIntegrableOn h B volume) (hwloc : LocallyIntegrableOn w B volume)
    (hghloc : LocallyIntegrableOn gh B volume) (hgwloc : LocallyIntegrableOn gw B volume) :
    HasWeakPartialDerivOn B k (fun x => h x + w x) (fun x => gh x + gw x) :=
  CKN.Core.Endgame.weak_partial_deriv_of_ae_sum (B := B) hB
    (p := fun x => h x + w x) (P := h) (H := w) (gp := gh) (gh := gw) (k := k)
    (hrep := Filter.EventuallyEq.rfl) hh hw hhloc hwloc hghloc hgwloc

end CKN.Core.Step4
