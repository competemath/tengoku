/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
module

public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.EnergyQuantities
public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialCutoffs
public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.WeakStationarity
public import Tengoku

/-!
# Weak radial integrability

This module contains the weak radial integrands and the integrability lemmas
that discharge the side conditions in the radial stationarity identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The main energy integrand in the weak radial identity at center `0`. -/
def weakRadialMainIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  weakRadialMainCoeff n phi x * weakEnergyDensity Du x

/-- The radial-energy integrand in the weak radial identity at center `0`. -/
def weakRadialRhsIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  weakRadialRhsCoeff phi x * weakRadialEnergyDensity Du 0 x

/-- Multiplication by an a.e. bounded scalar coefficient preserves integrability on a set.
@isnad1 id=integrab.3h5v.s10.f4a2e427b019 from=translated src=- shape=73d3177e vocab=6f18c1c4
-/
theorem integrableOn_bdd_mul_of_integrableOn {n : ℕ} {Ω : Set (Domain n)}
    {c g : Domain n → ℝ} {C : ℝ}
    (hg : IntegrableOn g Ω volume)
    (hc_meas : AEStronglyMeasurable c (volume.restrict Ω))
    (hc_bound : ∀ᵐ x ∂volume.restrict Ω, ‖c x‖ ≤ C) :
    IntegrableOn (fun x : Domain n => c x * g x) Ω volume := by
  exact hg.integrable.bdd_mul hc_meas hc_bound

/-- A function dominated in norm by an integrable scalar function is integrable on the set.
@isnad1 id=integrab.3h4v.s10.8c0662776f7c from=translated src=- shape=1f53e742 vocab=fce6c9dd
-/
theorem integrableOn_of_norm_le_integrableOn {n : ℕ} {Ω : Set (Domain n)}
    {f g : Domain n → ℝ}
    (hg : IntegrableOn g Ω volume)
    (hf_meas : AEStronglyMeasurable f (volume.restrict Ω))
    (hbound : ∀ᵐ x ∂volume.restrict Ω, ‖f x‖ ≤ g x) :
    IntegrableOn f Ω volume := by
  exact hg.integrable.mono' hf_meas hbound

/-- Radial energy is integrable once it is a.e. dominated by the weak energy density.
@isnad1 id=integrab.3h4v.s10.60b02e48e0fe from=translated src=- shape=8f8e1962 vocab=4b3b5c17
-/
theorem weakRadialEnergyDensity_integrableOn_of_energy_bound {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω))
    (hradial_bound :
      ∀ᵐ x ∂volume.restrict Ω,
        ‖weakRadialEnergyDensity Du (0 : Domain n) x‖ ≤ weakEnergyDensity Du x) :
    IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      Ω volume := by
  exact integrableOn_of_norm_le_integrableOn
    (n := n) (Ω := Ω)
    (f := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
    (g := fun x : Domain n => weakEnergyDensity Du x)
    henergy hradial_meas hradial_bound

/-- Radial energy is integrable on a set as soon as weak energy is integrable there,
provided the radial-energy density is a.e. strongly measurable.
@isnad1 id=integrab.2h4v.s9.6f75ca02850f from=translated src=- shape=cbdb1aed vocab=fb306e89
-/
theorem weakRadialEnergyDensity_integrableOn_of_energy {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω)) :
    IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      Ω volume := by
  exact weakRadialEnergyDensity_integrableOn_of_energy_bound
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    henergy hradial_meas
    (Filter.Eventually.of_forall fun x =>
      norm_weakRadialEnergyDensity_le_weakEnergyDensity Du (0 : Domain n) x)

/-- If the radial main coefficient is a.e. bounded and the weak energy is integrable,
then the main radial integrand is integrable.
@isnad1 id=integrab.3h6v.s10.49d999f88ca0 from=translated src=- shape=74f74ec0 vocab=0c3ea355
-/
theorem weakRadialMainIntegrand_integrableOn_of_bounded_coeff {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ} {C : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hcoeff_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hcoeff_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ C) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume := by
  simpa [weakRadialMainIntegrand] using
    integrableOn_bdd_mul_of_integrableOn
      (n := n) (Ω := Ω)
      (c := fun x : Domain n => weakRadialMainCoeff n phi x)
      (g := fun x : Domain n => weakEnergyDensity Du x)
      henergy hcoeff_meas hcoeff_bound

/-- If the radial right-hand coefficient is a.e. bounded and the weak radial energy
is integrable, then the right-hand radial integrand is integrable.
@isnad1 id=integrab.3h6v.s10.e6d283e37aac from=translated src=- shape=f886afa8 vocab=f09d8aed
-/
theorem weakRadialRhsIntegrand_integrableOn_of_bounded_coeff {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ} {C : ℝ}
    (hradial :
      IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        Ω volume)
    (hcoeff_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hcoeff_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ C) :
    IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  simpa [weakRadialRhsIntegrand] using
    integrableOn_bdd_mul_of_integrableOn
      (n := n) (Ω := Ω)
      (c := fun x : Domain n => weakRadialRhsCoeff phi x)
      (g := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      hradial hcoeff_meas hcoeff_bound

/-- A single package for the two integrability estimates needed in the weak radial identity.
@isnad1 id=and.6h7v.s11.5d3f9e0c02d3 from=translated src=- shape=062d0f08 vocab=6ca67391
-/
theorem weak_radial_cutoff_integrable_of_bounded_coefficients {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ}
    {Cmain Crhs : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial :
      IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        Ω volume)
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  exact
    ⟨weakRadialMainIntegrand_integrableOn_of_bounded_coeff
        (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
        henergy hmain_meas hmain_bound,
      weakRadialRhsIntegrand_integrableOn_of_bounded_coeff
        (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
        hradial hrhs_meas hrhs_bound⟩

/-- The two radial-integrability estimates using only weak-energy integrability,
provided radial energy is a.e. dominated by weak energy.
@isnad1 id=and.7h7v.s11.932d78612cc6 from=translated src=- shape=8f557dfb vocab=6ca67391
-/
theorem weak_radial_cutoff_integrable_of_energy_bound {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ}
    {Cmain Crhs : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω))
    (hradial_bound :
      ∀ᵐ x ∂volume.restrict Ω,
        ‖weakRadialEnergyDensity Du (0 : Domain n) x‖ ≤ weakEnergyDensity Du x)
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  have hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x) Ω volume :=
    weakRadialEnergyDensity_integrableOn_of_energy_bound
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      henergy hradial_meas hradial_bound
  exact weak_radial_cutoff_integrable_of_bounded_coefficients
    (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
    henergy hradial hmain_meas hmain_bound hrhs_meas hrhs_bound

/-- The two radial-integrability estimates using weak-energy integrability and
the pointwise bound `weakRadialEnergyDensity ≤ weakEnergyDensity`.
@isnad1 id=and.6h7v.s11.8d096fe5b907 from=translated src=- shape=85816673 vocab=6ca67391
-/
theorem weak_radial_cutoff_integrable_of_energy {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ}
    {Cmain Crhs : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω))
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  have hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x) Ω volume :=
    weakRadialEnergyDensity_integrableOn_of_energy
      (n := n) (m := m) (Du := Du) (Ω := Ω) henergy hradial_meas
  exact weak_radial_cutoff_integrable_of_bounded_coefficients
    (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
    henergy hradial hmain_meas hmain_bound hrhs_meas hrhs_bound

/-- The two radial-integrability estimates on a ball, with weak-gradient
measurability and weak-energy integrability supplied on a containing set.

The coefficient measurability comes from `ContDiff ℝ 1 phi`, and the a.e.
bounds come from pointwise bounds for `phi` and `phi'` on `[0, R0]`.
@isnad1 id=and.7h8v.s9.977f13fa8807 from=translated src=- shape=449006c4 vocab=1299a95a
-/
theorem weak_radial_cutoff_integrable_of_locallyL2 {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ} {phi : ℝ → ℝ}
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖phi t‖ ≤ M0)
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume := by
  have henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume :=
    gradientLocallyL2In_integrableOn_ball
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      hgrad hclosedBall_subset
  have hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)) :=
    weakRadialEnergyDensity_aestronglyMeasurable_on_ball_of_gradient
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      (a := 0) (r := R0) hDu_meas hclosedBall_subset
  exact weak_radial_cutoff_integrable_of_energy
    (n := n) (m := m) (Du := Du)
    (Ω := Metric.ball (0 : Domain n) R0) (phi := phi)
    (Cmain := ‖((n : ℝ) - 2)‖ * M0 + R0 * M1) (Crhs := R0 * M1)
    henergy hradial_meas
    (weakRadialMainCoeff_aestronglyMeasurable_of_contDiff
      (n := n) (Ω := Metric.ball (0 : Domain n) R0) hphi_c1)
    (weakRadialMainCoeff_ae_bound_on_ball_of_radius_bounds
      (n := n) (phi := phi) (R0 := R0) (M0 := M0) (M1 := M1)
      hphi_bound hdphi_bound hR0_nonneg)
    (weakRadialRhsCoeff_aestronglyMeasurable_of_contDiff
      (n := n) (Ω := Metric.ball (0 : Domain n) R0) hphi_c1)
    (weakRadialRhsCoeff_ae_bound_on_ball_of_radius_bound
      (n := n) (phi := phi) (R0 := R0) (M1 := M1)
      hdphi_bound hR0_nonneg)

/-- Cutoff-integrability on a ball, using the packaged cutoff interface.
@isnad1 id=and.4h8v.s9.4f2a9393502f from=translated src=- shape=968af6da vocab=62a8c5b9
-/
theorem weak_radial_cutoff_integrable_of_locallyL2_cutoff {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ} {phi : ℝ → ℝ}
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hcut : AdmissibleRadialCutoff n R0 M0 M1 phi) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume := by
  exact weak_radial_cutoff_integrable_of_locallyL2
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1) (phi := phi)
    hDu_meas hgrad hclosedBall_subset
    hcut.contDiff hcut.phi_bound hcut.deriv_bound hcut.radius_nonneg

/-- Cutoff-integrability on a ball from the `W^{1,2}_{loc}` interface.
@isnad1 id=and.3h9v.s9.1d08edf9bf92 from=translated src=- shape=16c663e5 vocab=5a37bd7b
-/
theorem weak_radial_cutoff_integrable_of_W12Loc_cutoff {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ} {phi : ℝ → ℝ}
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hcut : AdmissibleRadialCutoff n R0 M0 M1 phi) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume := by
  exact weak_radial_cutoff_integrable_of_locallyL2_cutoff
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1) (phi := phi)
    hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hcut

/-- Cutoff-integrability for a one-dimensional smooth bump cutoff.
@isnad1 id=and.3h7v.s9.d07238206603 from=translated src=- shape=b8917570 vocab=3d2e6525
-/
theorem weak_radial_cutoff_integrable_of_W12Loc_contDiffBump {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du (fun t : ℝ => f t) x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du (fun t : ℝ => f t) x)
        (Metric.ball (0 : Domain n) R0) volume := by
  rcases ContDiffBump.exists_admissibleRadialCutoff (n := n) f hRout with ⟨M1, hcut⟩
  exact weak_radial_cutoff_integrable_of_W12Loc_cutoff
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := 1) (M1 := M1)
    hW hclosedBall_subset hcut

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
