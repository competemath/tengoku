/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders

/-! # Morrey bounds from carrier-local representatives

Almost-everywhere equality on a measurable carrier transfers global bounds
of a representative to the indicated original function. The representative
need not vanish outside the carrier.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- Almost-everywhere equal scalar functions have the same cylinder Morrey norm. -/
theorem morreyNorm_eq_of_ae_eq {P τ : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) : morreyNorm P τ f = morreyNorm P τ g := by
  unfold morreyNorm
  congr 1
  funext z
  congr 1
  funext r
  unfold morreyCell cylinderPowerIntegral
  congr 2
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with w hw
  simp only [hw]

/-- A carrier-local representative bounds the indicated scalar Morrey norm. -/
theorem morreyNorm_indicator_le_of_ae_eq_restrict {P τ : ℝ} (hP : 0 ≤ P)
    {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → ℝ} (huv : u =ᵐ[volume.restrict Q] v) :
    morreyNorm P τ (Q.indicator u) ≤ morreyNorm P τ v := by
  rw [morreyNorm_eq_of_ae_eq ((ae_eq_restrict_iff_indicator_ae_eq hQ).mp huv)]
  exact morreyNorm_indicator_le hP Q v

/-- Component bounds transfer without imposing global equality to the representative. -/
theorem morreyNorm_component_indicator_le_of_ae_eq_restrict
    {P τ : ℝ} (hP : 0 ≤ P) {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → Vec3} (huv : u =ᵐ[volume.restrict Q] v)
    (i : Fin 3) :
    morreyNorm P τ (Q.indicator (fun z => u z i)) ≤
      morreyNorm P τ (fun z => v z i) := by
  apply morreyNorm_indicator_le_of_ae_eq_restrict hP hQ
  filter_upwards [huv] with z hz
  exact congrFun hz i

/-- A global Euclidean-norm bound controls every indicated component. -/
theorem morreyNorm_component_indicator_le_norm_of_ae_eq_restrict
    {P τ : ℝ} (hP : 0 ≤ P) {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → Vec3} (huv : u =ᵐ[volume.restrict Q] v)
    (i : Fin 3) :
    morreyNorm P τ (Q.indicator (fun z => u z i)) ≤
      morreyNorm P τ (fun z => vec3EuclideanNorm (v z)) := by
  apply (morreyNorm_component_indicator_le_of_ae_eq_restrict hP hQ huv i).trans
  apply morreyNorm_mono hP
  intro z
  rw [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v z j)) (Finset.mem_univ i)

end CKN.Core.Endgame
