/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalSources
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalLinearSources
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapLinearSources
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalForceSource
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability

/-! # Quantitative bounds for the actual gradient-slot source

The five terms of the localized equation are estimated from the improved
velocity norm, the initial gradient norm, the supplied pressure-gradient
norm, and the original force smallness. The formula includes the pressure
gradient in the order-two slot. No potential or Hölder estimate is assumed.
-/

@[expose] public section

section

/-! # The past-time convective heat source

The initial velocity exponent and initial gradient exponent give the
convective source estimate by scalar Morrey Hölder and the finite-sum
triangle inequality. Only the cutoff's nonpositive-time values are used.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

end CKN.Core.Endgame
end

end

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- Every component of the velocity, weak gradient, pressure, and force,
indicated to the intermediate one-sided cylinder, is globally a.e.
measurable. All measurability is supplied by the local solution clauses. -/
theorem bootstrap_indicated_components_aemeasurable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hunit : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I) :
    (∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z i)) volume) ∧
    (∀ i j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) volume) ∧
    AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator p) volume ∧
    ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => f z i)) volume := by
  obtain ⟨Ω', J, hbox, _hJopen, hunitbox⟩ :=
    exists_localBox_around_closed_unit hsol.1 hsol.2.1 hunit
  have hsub : parabolicCylinder (0 : Vec3) 0 (11 / 16) ⊆ spaceTimeSet Ω' J :=
    (parabolicCylinder_mono (by norm_num : (0 : ℝ) ≤ 11 / 16)
      (by norm_num : (11 / 16 : ℝ) ≤ 1)).trans (subset_closure.trans hunitbox)
  have hmeasure := Measure.restrict_mono (μ := volume) hsub le_rfl
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hu := hdata.1.aemeasurable.mono_measure hmeasure
  have hDu := hdata.2.1.aemeasurable.mono_measure hmeasure
  have hp := hdata.2.2.1.aemeasurable.mono_measure hmeasure
  have hf := hdata.2.2.2.1.aemeasurable.mono_measure hmeasure
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (11 / 16)) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  refine ⟨?_, ?_, (aemeasurable_indicator_iff hS).mpr hp, ?_⟩
  · intro i
    exact (aemeasurable_indicator_iff hS).mpr (aemeasurable_pi_iff.mp hu i)
  · intro i j
    exact (aemeasurable_indicator_iff hS).mpr
      (aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hDu i) j)
  · intro i
    exact (aemeasurable_indicator_iff hS).mpr (aemeasurable_pi_iff.mp hf i)

/-- Past cutoff coefficients vanish outside the larger initial cylinder. -/
theorem bootstrap_cutoff_coefficients_zero
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (11 / 16))
    {z : ParabolicPoint} (ht : z.2 ≤ 0)
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16)) :
    φ z = 0 ∧ timePartial φ z = 0 ∧
      (∀ j, spatialPartial φ j z = 0) ∧
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
  have hraw : (z.1, z.2) ∉ tsupport φ := fun hmem => hz (hsupp _ hmem ht)
  have hvalue : φ (z.1, z.2) = 0 := image_eq_zero_of_notMem_tsupport hraw
  refine ⟨hvalue,
    timePartial_zero_of_not_mem_tsupport_public hφ hraw,
    fun j => spatialPartial_zero_of_not_mem_tsupport_public hφ hraw j, ?_⟩
  change (∑ j, spatialSecondPartial φ j j z) = 0
  exact Finset.sum_eq_zero fun j _ =>
    spatialSecondPartial_zero_of_not_mem_tsupport_public hφ hraw j j

/-- Both literal source slots vanish outside any cylinder containing the
cutoff's past support. This statement also applies to the smaller support
cylinder used inside the initial norm carrier. -/
theorem bootstrap_literal_sources_zero_on_past
    {R : ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 R)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f Dp : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (ht : z.2 ≤ 0) (hz : z ∉ parabolicCylinder (0 : Vec3) 0 R) :
    CKN.Core.Step4.localizedGradientSourceG φ u Du f Dp z = 0 ∧
      ∀ j, CKN.Core.Step4.localizedGradientSourceH φ u j z = 0 := by
  have hraw : (z.1, z.2) ∉ tsupport φ := fun hm => hz (hsupp _ hm ht)
  have hv : φ (z.1, z.2) = 0 := image_eq_zero_of_notMem_tsupport hraw
  have ht' : timePartial φ z = 0 := timePartial_zero_of_not_mem_tsupport_public hφ hraw
  have hx : ∀ j, spatialPartial φ j z = 0 :=
    fun j => spatialPartial_zero_of_not_mem_tsupport_public hφ hraw j
  have hlap : spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    change (∑ j, spatialSecondPartial φ j j z) = 0
    exact Finset.sum_eq_zero fun j _ =>
      spatialSecondPartial_zero_of_not_mem_tsupport_public hφ hraw j j
  constructor
  · funext i
    change timePartial φ z * u z i +
      spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i -
      φ z * localizedConvection u Du z i + φ z * f z i - φ z * Dp z i = 0
    change φ z = 0 at hv
    simp only [ht', hlap, hv, zero_mul, add_zero, sub_zero]
  · intro j
    funext i
    change (-2 * spatialPartial φ j z) * u z i = 0
    rw [hx j, mul_zero, zero_mul]

/-- The numerical bound for a component of the first order-two source. -/
def bootstrapGradientMorreyBound (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    3 * KU * KD + forceSourceMorreyBound q ε₀ + KP

/-- Finite input bounds give a finite numerical source bound. -/
theorem bootstrapGradientMorreyBound_lt_top
    (q ε₀ C : ℝ) {KU KD KP : ℝ≥0∞} (hq : 5 / 2 < q)
    (hKU : KU < ⊤) (hKD : KD < ⊤) (hKP : KP < ⊤) :
    bootstrapGradientMorreyBound q ε₀ C KU KD KP < ⊤ := by
  have hvol : volume (parabolicCylinder (0 : Vec3) 0 1) ^ (5 / 6 - 1 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne
  have hforce := forceSourceMorreyBound_lt_top q ε₀ hq
  unfold bootstrapGradientMorreyBound
  finiteness

private theorem norm_neg {P τ : ℝ} (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => -f z) = morreyNorm P τ f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private theorem norm_sub_le {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z - g z) ≤ morreyNorm P τ f + morreyNorm P τ g := by
  have h := morrey_norm_add_le (τ := τ) hP hf hg.neg
  change morreyNorm P τ (fun z => f z + -g z) ≤
    morreyNorm P τ f + morreyNorm P τ (fun z => -g z) at h
  rw [norm_neg] at h
  simpa only [sub_eq_add_neg] using h

end CKN.Core.Endgame
