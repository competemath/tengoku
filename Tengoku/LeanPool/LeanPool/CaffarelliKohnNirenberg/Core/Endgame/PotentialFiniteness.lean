/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.AdamsConstants

/-! # Almost-everywhere finiteness of subcritical potentials

Bounded support turns a finite Morrey norm into a finite global power
integral. The maximal estimate and the unoptimized Hedberg estimate then
give finiteness of the extended-real potential almost everywhere, before
any use of its real-valued conversion.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Endgame

/-- A bounded-support Morrey source has finite global power integral. -/
theorem source_power_integral_lt_top
    {P τ R : ℝ} (hP : 0 < P) (hR : 0 < R)
    {z₀ : ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hN : morreyNorm P τ f < ∞)
    (hsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, f z = 0) :
    (∫⁻ z, ENNReal.ofReal |f z| ^ P) < ∞ := by
  have heq : (fun z => ENNReal.ofReal |f z| ^ P) =
      (parabolicCylinder z₀.1 z₀.2 R).indicator
        (fun z => ENNReal.ofReal |f z| ^ P) := by
    funext z
    by_cases hz : z ∈ parabolicCylinder z₀.1 z₀.2 R
    · simp [hz]
    · simp [hz, hsupp z hz, ENNReal.zero_rpow_of_pos hP]
  have hset : MeasurableSet (parabolicCylinder z₀.1 z₀.2 R) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  rw [heq, lintegral_indicator hset]
  have hbound := cylinderPowerIntegral_le_morreyNorm_pow (q := τ) hP hf hR
    (z := z₀)
  apply hbound.trans_lt
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top))
    (ENNReal.rpow_lt_top_of_nonneg hP.le hN.ne)

/-- Almost-everywhere changes of a scalar source preserve its Morrey norm. -/
theorem morrey_norm_congr_ae {P τ : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) : morreyNorm P τ f = morreyNorm P τ g := by
  unfold morreyNorm
  congr 1
  funext z
  congr 1
  funext r
  unfold morreyCell
  congr 2
  unfold cylinderPowerIntegral
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with w hw
  rw [hw]

/-- Almost-everywhere changes of a source preserve the extended-real
potential at every evaluation point. -/
theorem riesz_potential_congr_ae {β : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) (z : ParabolicPoint) :
    parabolicRieszPotential β f z = parabolicRieszPotential β g z := by
  unfold parabolicRieszPotential
  apply lintegral_congr_ae
  filter_upwards [hfg] with w hw
  rw [hw]

end CKN.Core.Endgame
