/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Pressure slices with an actual weak gradient

The particular gradient is supplied as a measurable field with its weak
identity. Only the test functions are differentiated classically.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Endgame

private theorem integrableOn_mul_test
    {B : Set Vec3} (hB : IsOpen B) {f ψ : Vec3 → ℝ}
    (hf : LocallyIntegrableOn f B volume) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ B) :
    IntegrableOn (fun x => f x * ψ x) B volume := by
  have hm := hf.mul_continuousOn hψ.continuousOn hB.isLocallyClosed
  have hk := hm.integrableOn_compact_subset hψB hψc.isCompact
  have hg := hk.integrable_of_forall_notMem_eq_zero (by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])
  exact hg.integrableOn

/-- Addition of locally integrable weak derivatives respects an a.e.
decomposition of the underlying pressure. -/
theorem weak_partial_deriv_of_ae_sum
    {B : Set Vec3} (hB : IsOpen B) {p P H gp gh : Vec3 → ℝ} {k : Fin 3}
    (hrep : p =ᵐ[volume.restrict B] P + H)
    (hP : HasWeakPartialDerivOn B k P gp)
    (hH : HasWeakPartialDerivOn B k H gh)
    (hPloc : LocallyIntegrableOn P B volume)
    (hHloc : LocallyIntegrableOn H B volume)
    (hgploc : LocallyIntegrableOn gp B volume)
    (hghloc : LocallyIntegrableOn gh B volume) :
    HasWeakPartialDerivOn B k p (gp + gh) := by
  intro ψ hψ hψc hψB
  have hd : Continuous (fun x => (fderiv ℝ ψ x) (basisVec k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => (fderiv ℝ ψ x) (basisVec k)) :=
    hψc.mono' (subset_closure.trans
      (tsupport_fderiv_apply_subset ℝ (basisVec k)))
  have hdB : tsupport (fun x => (fderiv ℝ ψ x) (basisVec k)) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec k)).trans hψB
  have hleft : (∫ x in B, p x * (fderiv ℝ ψ x) (basisVec k)) =
      ∫ x in B, (P x + H x) * (fderiv ℝ ψ x) (basisVec k) := by
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
    rfl
  rw [hleft]
  simp_rw [Pi.add_apply, add_mul]
  rw [integral_add (integrableOn_mul_test hB hPloc hd hdc hdB)
      (integrableOn_mul_test hB hHloc hd hdc hdB),
    integral_add (integrableOn_mul_test hB hgploc hψ.continuous hψc hψB)
      (integrableOn_mul_test hB hghloc hψ.continuous hψc hψB),
    hP ψ hψ hψc hψB, hH ψ hψ hψc hψB]
  ring

/-- A whole-space weak pairing restricts to any open slice domain. -/
theorem weak_partial_deriv_on_of_global_pairing
    {B : Set Vec3} (hB : IsOpen B) {P D : Vec3 → ℝ} {k : Fin 3}
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, P x * spatialDeriv ψ k x) = -(∫ x, D x * ψ x)) :
    HasWeakPartialDerivOn B k P D := by
  have hglobal : HasWeakPartialDerivOn Set.univ k P D := by
    intro ψ hψ hψc _
    simpa only [Measure.restrict_univ, spatialDeriv] using hweak ψ hψ hψc
  exact hglobal.restrict hB (subset_univ B)

end CKN.Core.Endgame
