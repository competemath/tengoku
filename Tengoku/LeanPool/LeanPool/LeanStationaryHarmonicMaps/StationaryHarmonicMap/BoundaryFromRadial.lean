/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
module

public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusAnalysis
import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusFormulas
public import Tengoku

/-!
# Boundary identity from radial stationarity

This module turns one-dimensional cutoff, coarea, and integration-by-parts
inputs into the weak boundary identity.

The theorems here are internal scaffolding for the proof route from radial
stationarity to the boundary identity.  The recommended public entry point is
the final theorem in `MainTheorem.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Energy integration by parts plus integrability of the expanded terms gives
the concrete one-dimensional IBP formula used downstream.
@isnad1 id=weakoned.2h4v.s4.36d61a87f30b from=translated src=- shape=8dce662f vocab=20e0369e
-/
theorem weakOneDimensionalIBPFormula_of_energyIBP {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (henergy_ibp : WeakBallEnergyIntegrationByPartsFormula Du R0)
    (hint : WeakOneDimensionalIBPIntegrability Du R0) :
    WeakOneDimensionalIBPFormula Du R0 := by
  intro phi hphi_diff hphi_cont hphi_compact hphi_support
  let s : Set ℝ := Ioo (0 : ℝ) R0
  let E : ℝ → ℝ := weakBallEnergy Du (0 : Domain n)
  let Q : ℝ → ℝ := weakBallRadialEnergy Du (0 : Domain n)
  let A : ℝ → ℝ := fun rho => (((n : ℝ) - 2) * phi rho) * deriv E rho
  let B : ℝ → ℝ := fun rho => (rho * deriv phi rho) * deriv E rho
  let C : ℝ → ℝ := fun rho => (rho * deriv phi rho) * deriv Q rho
  let D : ℝ → ℝ := fun rho => (-deriv phi rho) * (((n : ℝ) - 2) * E rho)
  rcases hint phi hphi_diff hphi_cont hphi_compact hphi_support with
    ⟨hD_int, hA_int, hB_int, hC_int⟩
  have hmain_eq :
      (∫ rho in s, weakRadialOneDimensionalMainIntegrand Du phi rho)
        =
      (∫ rho in s, A rho + B rho) := by
    apply integral_congr_ae
    filter_upwards with rho
    simp [A, B, E, weakRadialOneDimensionalMainIntegrand]
    ring
  have hmain_split :
      (∫ rho in s, A rho + B rho)
        =
      (∫ rho in s, A rho) + (∫ rho in s, B rho) := by
    exact integral_add hA_int.integrable hB_int.integrable
  have hdefect_eq :
      (∫ rho in s,
          (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho)
        =
      (∫ rho in s, D rho + B rho - 2 * C rho) := by
    apply integral_congr_ae
    filter_upwards with rho
    simp [D, B, C, E, Q, weakSharpCutoffDefect]
    ring
  have hDB_int : Integrable (fun rho : ℝ => D rho + B rho) (volume.restrict s) :=
    hD_int.integrable.add hB_int.integrable
  have htwoC_int : Integrable (fun rho : ℝ => 2 * C rho) (volume.restrict s) :=
    hC_int.integrable.const_mul 2
  have hdefect_split :
      (∫ rho in s, D rho + B rho - 2 * C rho)
        =
      (∫ rho in s, D rho) + (∫ rho in s, B rho) -
        2 * ∫ rho in s, C rho := by
    rw [integral_sub hDB_int htwoC_int]
    rw [integral_add hD_int.integrable hB_int.integrable]
    rw [integral_const_mul]
  have hD_eq_A :
      (∫ rho in s, D rho) = (∫ rho in s, A rho) := by
    simpa [s, D, A, E] using
      henergy_ibp phi hphi_diff hphi_cont hphi_compact hphi_support
  calc
    (∫ rho in Ioo (0 : ℝ) R0,
      (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho)
        =
      (∫ rho in s, D rho + B rho - 2 * C rho) := hdefect_eq
    _ =
      (∫ rho in s, D rho) + (∫ rho in s, B rho) -
        2 * ∫ rho in s, C rho := hdefect_split
    _ =
      (∫ rho in s, A rho) + (∫ rho in s, B rho) -
        2 * ∫ rho in s, C rho := by rw [hD_eq_A]
    _ =
      (∫ rho in s, A rho + B rho) -
        2 * ∫ rho in s, C rho := by rw [hmain_split]
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        weakRadialOneDimensionalMainIntegrand Du phi rho)
        -
      2 * ∫ rho in Ioo (0 : ℝ) R0,
        weakRadialOneDimensionalRhsIntegrand Du phi rho := by
        rw [hmain_eq]
        rfl

/-- The packaged one-dimensional calculus input gives the concrete IBP formula
used by the defect-to-distribution argument.
@isnad1 id=weakoned.1h4v.s4.3a8cb9364d47 from=translated src=- shape=cc25598c vocab=f9418d36
-/
theorem weakOneDimensionalIBPFormula_of_energy_calculus {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0) :
    WeakOneDimensionalIBPFormula Du R0 := by
  exact weakOneDimensionalIBPFormula_of_energyIBP
    (n := n) (m := m) (Du := Du) (R0 := R0)
    (weakBallEnergyIntegrationByPartsFormula_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    (weakOneDimensionalIBPIntegrability_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)

/-- Direct distributional sharp-cutoff identity from weak stationarity, using
only the primitive cutoffs constructed for the given one-dimensional test
function.  This avoids any global regularity assumption on all scalar cutoffs:
the constructed primitive is constant near the origin, so its radial vector
field is admissible.
@isnad1 id=weakshar.8h6v.s8.bd12742c47b8 from=translated src=- shape=f9559504 vocab=bf262b71
-/
theorem weakSharpCutoffDistributionIdentity_from_stationarity_of_W12Loc_primitives
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakSharpCutoffDistributionIdentity Du (0 : Domain n) R0 := by
  intro g hg_smooth hg_compact hg_support
  rcases hprimitive_realize g hg_smooth hg_compact hg_support with
    ⟨phi, hphi_diff, hphi_cont, hphi_compact, hphi_support,
      hphi_const, hderiv_ae⟩
  rcases exists_admissibleRadialCutoff_of_contDiff_const_near_origin
      (n := n) (R0 := R0) (phi := phi)
      hR0_nonneg hphi_diff hphi_cont hphi_compact hphi_support
      hphi_const with
    ⟨M0, M1, hcut⟩
  have hspace :
      (∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialMainIntegrand Du phi x)
        =
      2 * ∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialRhsIntegrand Du phi x :=
    weak_radial_identity_from_stationarity_of_W12Loc_cutoff
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
      (R0 := R0) (M0 := M0) (M1 := M1)
      hstationary hW hclosedBall_subset hcut
  have hcoarea : WeakRadialCoareaIntegralFormula Du R0 :=
    weakRadialCoareaIntegralFormula_of_radiusIntegral
      (n := n) (m := m) (Du := Du) (R0 := R0)
      henergy_radius hradial_radius
  rcases hcoarea phi hphi_diff hphi_cont hphi_compact hphi_support with
    ⟨hmain, hrhs⟩
  have hone_phi :
      (∫ rho in Ioo (0 : ℝ) R0,
          weakRadialOneDimensionalMainIntegrand Du phi rho)
        =
      2 * ∫ rho in Ioo (0 : ℝ) R0,
          weakRadialOneDimensionalRhsIntegrand Du phi rho := by
    rw [← hmain, hspace, hrhs]
  have hibp_formula : WeakOneDimensionalIBPFormula Du R0 :=
    weakOneDimensionalIBPFormula_of_energy_calculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc
  have hderiv_zero :
      (∫ rho in Ioo (0 : ℝ) R0,
        (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho) = 0 := by
    rw [hibp_formula phi hphi_diff hphi_cont hphi_compact hphi_support]
    rw [hone_phi]
    ring
  let defect : ℝ → ℝ := fun rho =>
    weakSharpCutoffDefect Du (0 : Domain n) rho
  have hg_zero :
      ∀ rho : ℝ, rho ∉ Ioo (0 : ℝ) R0 → g rho • defect rho = 0 := by
    intro rho hrho
    have hrho_not_support : rho ∉ tsupport g := by
      intro hrho_support
      exact hrho (hg_support hrho_support)
    have hg_rho : g rho = 0 := image_eq_zero_of_notMem_tsupport hrho_not_support
    simp [defect, hg_rho]
  calc
    (∫ rho : ℝ, g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        g rho • weakSharpCutoffDefect Du (0 : Domain n) rho) := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Ioo (0 : ℝ) R0)
          (f := fun rho : ℝ =>
            g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
          hg_zero
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho) := by
        apply integral_congr_ae
        filter_upwards [hderiv_ae] with rho hderiv
        simp [hderiv, smul_eq_mul]
    _ = 0 := hderiv_zero

/-- Restricted-weight version of the direct distributional sharp-cutoff
identity from weak stationarity and primitive cutoffs.
@isnad1 id=weakshar.8h6v.s8.46e6cad83325 from=translated src=- shape=f9559504 vocab=ebdf2e23
-/
theorem weakSharpCutoffDistributionIdentity_from_stationarity_of_W12Loc_primitivesForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakSharpCutoffDistributionIdentity Du (0 : Domain n) R0 := by
  intro g hg_smooth hg_compact hg_support
  rcases hprimitive_realize g hg_smooth hg_compact hg_support with
    ⟨phi, hphi_diff, hphi_cont, hphi_compact, hphi_support,
      hphi_const, hderiv_ae⟩
  rcases exists_admissibleRadialCutoff_of_contDiff_const_near_origin
      (n := n) (R0 := R0) (phi := phi)
      hR0_nonneg hphi_diff hphi_cont hphi_compact hphi_support
      hphi_const with
    ⟨M0, M1, hcut⟩
  have hspace :
      (∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialMainIntegrand Du phi x)
        =
      2 * ∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialRhsIntegrand Du phi x :=
    weak_radial_identity_from_stationarity_of_W12Loc_cutoff
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
      (R0 := R0) (M0 := M0) (M1 := M1)
      hstationary hW hclosedBall_subset hcut
  have hcoarea : WeakRadialCoareaIntegralFormula Du R0 :=
    weakRadialCoareaIntegralFormula_of_radiusIntegralForWeights
      (n := n) (m := m) (Du := Du) (R0 := R0)
      henergy_radius hradial_radius
  rcases hcoarea phi hphi_diff hphi_cont hphi_compact hphi_support with
    ⟨hmain, hrhs⟩
  have hone_phi :
      (∫ rho in Ioo (0 : ℝ) R0,
          weakRadialOneDimensionalMainIntegrand Du phi rho)
        =
      2 * ∫ rho in Ioo (0 : ℝ) R0,
          weakRadialOneDimensionalRhsIntegrand Du phi rho := by
    rw [← hmain, hspace, hrhs]
  have hibp_formula : WeakOneDimensionalIBPFormula Du R0 :=
    weakOneDimensionalIBPFormula_of_energy_calculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc
  have hderiv_zero :
      (∫ rho in Ioo (0 : ℝ) R0,
        (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho) = 0 := by
    rw [hibp_formula phi hphi_diff hphi_cont hphi_compact hphi_support]
    rw [hone_phi]
    ring
  let defect : ℝ → ℝ := fun rho =>
    weakSharpCutoffDefect Du (0 : Domain n) rho
  have hg_zero :
      ∀ rho : ℝ, rho ∉ Ioo (0 : ℝ) R0 → g rho • defect rho = 0 := by
    intro rho hrho
    have hrho_not_support : rho ∉ tsupport g := by
      intro hrho_support
      exact hrho (hg_support hrho_support)
    have hg_rho : g rho = 0 := image_eq_zero_of_notMem_tsupport hrho_not_support
    simp [defect, hg_rho]
  calc
    (∫ rho : ℝ, g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        g rho • weakSharpCutoffDefect Du (0 : Domain n) rho) := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Ioo (0 : ℝ) R0)
          (f := fun rho : ℝ =>
            g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
          hg_zero
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho) := by
        apply integral_congr_ae
        filter_upwards [hderiv_ae] with rho hderiv
        simp [hderiv, smul_eq_mul]
    _ = 0 := hderiv_zero

/-- Boundary identity from weak stationarity through the primitive-cutoff
distributional route.  The only one-dimensional analytic input is the packaged
radius energy calculus; no global `hflat`/`hX` hypothesis is needed.
@isnad1 id=weakboun.9h6v.s8.022b4dbda551 from=translated src=- shape=a9b41beb vocab=0503a28c
-/
theorem weak_boundary_identity_from_stationarity_of_W12Loc_via_primitives
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  have hdist : WeakSharpCutoffDistributionIdentity Du (0 : Domain n) R0 :=
    weakSharpCutoffDistributionIdentity_from_stationarity_of_W12Loc_primitives
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary hW hclosedBall_subset
      henergy_radius hradial_radius hcalc hprimitive_realize
  exact weakBoundaryIdentity_of_sharpCutoffLimit
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (weakSharpCutoffLimitIdentity_of_distribution
      (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
      hdefect_loc hdist)

/-- Restricted-weight version of the boundary identity from weak stationarity
through the primitive-cutoff distributional route.
@isnad1 id=weakboun.9h6v.s8.a910a5e9678d from=translated src=- shape=a9b41beb vocab=0bf5c5b9
-/
theorem weak_boundary_identity_from_stationarity_of_W12Loc_via_primitivesForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  have hdist : WeakSharpCutoffDistributionIdentity Du (0 : Domain n) R0 :=
    weakSharpCutoffDistributionIdentity_from_stationarity_of_W12Loc_primitivesForWeights
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary hW hclosedBall_subset
      henergy_radius hradial_radius hcalc hprimitive_realize
  exact weakBoundaryIdentity_of_sharpCutoffLimit
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (weakSharpCutoffLimitIdentity_of_distribution
      (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
      hdefect_loc hdist)

/-- A concrete integration-by-parts formula discharges the abstract one
dimensional IBP step.
@isnad1 id=weakoned.1h4v.s4.e8bea61b4dae from=translated src=- shape=cc25598c vocab=d1e0f12e
-/
theorem weakOneDimensionalIBPStep_of_formula {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0) :
    WeakOneDimensionalIBPStep Du R0 := by
  intro hone phi hphi_diff hphi_cont hphi_compact hphi_support
  have hone_phi :
      (∫ rho in Ioo (0 : ℝ) R0,
          weakRadialOneDimensionalMainIntegrand Du phi rho)
        =
      2 * ∫ rho in Ioo (0 : ℝ) R0,
          weakRadialOneDimensionalRhsIntegrand Du phi rho :=
    hone phi hphi_diff hphi_cont hphi_compact hphi_support
  rw [hibp_formula phi hphi_diff hphi_cont hphi_compact hphi_support]
  linarith

/-- Once the defect pairs to zero against all primitive cutoff derivatives, the
primitive family gives the full distributional sharp-cutoff identity.
@isnad1 id=weakshar.2h4v.s6.578728f44b12 from=translated src=- shape=94a40ef4 vocab=8b796aae
-/
theorem weakSharpCutoffDistributionIdentity_of_derivative_identity {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hderiv : WeakOneDimensionalDefectDerivativeIdentity Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakSharpCutoffDistributionIdentity Du (0 : Domain n) R0 := by
  intro g hg_smooth hg_compact hg_support
  rcases hprimitive g hg_smooth hg_compact hg_support with
    ⟨phi, hphi_diff, hphi_cont, hphi_compact, hphi_support, hg_eq⟩
  rw [hg_eq]
  exact hderiv phi hphi_diff hphi_cont hphi_compact hphi_support

/-- Factored version of the one-dimensional sharp-cutoff-to-distribution step:
first integrate by parts, then use primitive cutoffs for arbitrary test
functions.
@isnad1 id=weakoned.2h4v.s4.0e1355002b63 from=translated src=- shape=8dce662f vocab=6989c4e0
-/
theorem weakOneDimensionalToDistributionStep_of_ibp_and_primitives {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hibp : WeakOneDimensionalIBPStep Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakOneDimensionalToDistributionStep Du R0 := by
  intro hone
  exact weakSharpCutoffDistributionIdentity_of_derivative_identity
    (n := n) (m := m) (Du := Du) (R0 := R0)
    (hibp hone) hprimitive

/-- The distributional one-dimensional cutoff step, plus local integrability of
the defect, gives the a.e. sharp-cutoff step.
@isnad1 id=weakoned.2h4v.s7.02c9ad7e3c1a from=translated src=- shape=97d036ee vocab=d6dbc188
-/
theorem weakOneDimensionalSharpCutoffStep_of_distribution {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hdist : WeakOneDimensionalToDistributionStep Du R0) :
    WeakOneDimensionalSharpCutoffStep Du R0 := by
  intro hone
  exact weakSharpCutoffLimitIdentity_of_distribution
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    hdefect_loc (hdist hone)

/-- The cutoff-limit step can be factored into coarea/radius differentiation
followed by a one-dimensional sharp-cutoff approximation.
@isnad1 id=weakradi.2h4v.s4.b24066950750 from=translated src=- shape=8dce662f vocab=655324a1
-/
theorem weakRadialCutoffLimitStep_of_coarea_and_oneDimensional {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcoarea : WeakRadialCoareaDerivativeStep Du R0)
    (hsharp : WeakOneDimensionalSharpCutoffStep Du R0) :
    WeakRadialCutoffLimitStep Du R0 := by
  intro hrad
  exact hsharp (hcoarea hrad)

/-- Step 1: compute the derivative and divergence of `X(x) = phi(|x|) x`.

In the full proof this should produce the integrand
`((n - 2) * phi |x| + |x| * phi' |x|) * |du|^2
 - 2 * |x| * phi' |x| * |partial_r u|^2`.
@isnad1 id=and.1h4v.s6.d7551b3964d3 from=translated src=- shape=921db415 vocab=fd87a874
-/
theorem radial_vector_field_computation {n m : ℕ}
    (u : Domain n → Target m) (phi : ℝ → ℝ)
    (hphi : Differentiable ℝ phi) :
    RadialVectorFieldDerivativeFormula (n := n) phi ∧
      RadialVectorFieldDivergenceFormula (n := n) phi ∧
      RadialStressContractionFormula u phi := by
  exact ⟨radialVectorFieldDerivativeFormula hphi,
    radialVectorFieldDivergenceFormula hphi,
    radialStressContractionFormula u hphi⟩

/-- Step 2: stationarity implies the radial identity.
@isnad1 id=radialst.3h4v.s7.883f8d75955e from=translated src=- shape=bf09ae09 vocab=d28d3d04
-/
theorem radial_identity_from_stationarity {n m : ℕ}
    {u : Domain n → Target m} {R0 : ℝ}
    (hstationary : SmoothStationaryIn u (Metric.ball (0 : Domain n) R0))
    (halgebra :
      ∀ phi : ℝ → ℝ,
        RadialVectorFieldDivergenceFormula (n := n) phi ∧
          RadialStressContractionFormula u phi)
    (hderive :
      SmoothStationaryIn u (Metric.ball (0 : Domain n) R0) →
        (∀ phi : ℝ → ℝ,
          RadialVectorFieldDivergenceFormula (n := n) phi ∧
            RadialStressContractionFormula u phi) →
        RadialStationarityIdentity u R0) :
    RadialStationarityIdentity u R0 := by
  exact hderive hstationary halgebra

/-- Step 3: approximate the sharp radial cutoff and pass to Lebesgue points.
@isnad1 id=boundary.2h4v.s7.aca701fc47e5 from=translated src=- shape=6b117263 vocab=533e6da7
-/
theorem boundary_identity_from_radial_identity {n m : ℕ}
    {u : Domain n → Target m} {R0 : ℝ}
    (hrad : RadialStationarityIdentity u R0)
    (hderive :
      RadialStationarityIdentity u R0 →
        BoundaryIdentity u (0 : Domain n) R0) :
    BoundaryIdentity u (0 : Domain n) R0 := by
  exact hderive hrad

/-- Weak version of the cutoff-to-boundary step: the radial stationarity identity
is first converted into the sharp-cutoff a.e. radius identity, then algebraically
rewritten as the weak boundary identity.
@isnad1 id=weakboun.2h4v.s6.0099c8e1001e from=translated src=- shape=94a40ef4 vocab=da2dea30
-/
theorem weak_boundary_identity_from_radial_identity {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hcutoff : WeakRadialCutoffLimitStep Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weakBoundaryIdentity_of_sharpCutoffLimit (hcutoff hrad)

/-- The full weak radial-to-boundary route, with the two analytic ingredients
kept separate: coarea/radius differentiation and one-dimensional sharp cutoffs.
@isnad1 id=weakboun.3h4v.s6.f288ee0069fa from=translated src=- shape=ff178036 vocab=4c843763
-/
theorem weak_boundary_identity_from_radial_identity_via_coarea {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hcoarea : WeakRadialCoareaDerivativeStep Du R0)
    (hsharp : WeakOneDimensionalSharpCutoffStep Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity
    (n := n) (m := m) (Du := Du) (R0 := R0) hrad
    (weakRadialCutoffLimitStep_of_coarea_and_oneDimensional
      (n := n) (m := m) (Du := Du) (R0 := R0) hcoarea hsharp)

/-- Fully factored weak radial-to-boundary route: a concrete coarea/radius
formula plus the one-dimensional distributional sharp-cutoff argument imply the
weak boundary identity.
@isnad1 id=weakboun.4h4v.s7.8a2208fcc702 from=translated src=- shape=66d9fdc9 vocab=881ef698
-/
theorem weak_boundary_identity_from_radial_identity_via_formula_and_distribution {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hcoarea_formula : WeakRadialCoareaDerivativeFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hdist : WeakOneDimensionalToDistributionStep Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity_via_coarea
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad
    (weakRadialCoareaDerivativeStep_of_formula
      (n := n) (m := m) (Du := Du) (R0 := R0) hcoarea_formula)
    (weakOneDimensionalSharpCutoffStep_of_distribution
      (n := n) (m := m) (Du := Du) (R0 := R0) hdefect_loc hdist)

/-- Even more granular weak radial-to-boundary route: after the coarea/radius
formula, the one-dimensional sharp-cutoff part is split into integration by
parts and primitive cutoff construction.
@isnad1 id=weakboun.5h4v.s7.250e1bca874d from=translated src=- shape=ef3fdd06 vocab=db1940ec
-/
theorem weak_boundary_identity_from_radial_identity_via_formula_ibp_primitives {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hcoarea_formula : WeakRadialCoareaDerivativeFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp : WeakOneDimensionalIBPStep Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity_via_formula_and_distribution
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad hcoarea_formula hdefect_loc
    (weakOneDimensionalToDistributionStep_of_ibp_and_primitives
      (n := n) (m := m) (Du := Du) (R0 := R0) hibp hprimitive)

/-- Version of the previous route using the concrete one-dimensional
integration-by-parts formula.
@isnad1 id=weakboun.5h4v.s7.41515d1b6449 from=translated src=- shape=ef3fdd06 vocab=96e68af2
-/
theorem weak_boundary_identity_from_radial_identity_via_formula_ibpFormula_primitives {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hcoarea_formula : WeakRadialCoareaDerivativeFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity_via_formula_ibp_primitives
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad hcoarea_formula hdefect_loc
    (weakOneDimensionalIBPStep_of_formula
      (n := n) (m := m) (Du := Du) (R0 := R0) hibp_formula)
    hprimitive

/-- The most decomposed route currently used by the formalization: vector-field
regularity, coarea/radius integration, one-dimensional IBP, and primitive
cutoffs are independent ingredients.
@isnad1 id=weakboun.6h4v.s7.7c93fcd67966 from=translated src=- shape=e465bbb8 vocab=980dbf43
-/
theorem weak_boundary_identity_from_radial_identity_via_split_ingredients {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hX : RadialVectorFieldContDiffForCutoffs n R0)
    (hcoarea_integral : WeakRadialCoareaIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity_via_formula_ibpFormula_primitives
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad
    (weakRadialCoareaDerivativeFormula_of_contDiff_and_integral
      (n := n) (m := m) (Du := Du) (R0 := R0) hX hcoarea_integral)
    hdefect_loc hibp_formula hprimitive

/-- Same fully decomposed route, with radial vector-field regularity discharged
from the natural flat-at-origin condition on scalar cutoffs.
@isnad1 id=weakboun.6h4v.s7.8ab266f80a2b from=translated src=- shape=909b8d62 vocab=96f2cc52
-/
theorem weak_boundary_identity_from_radial_identity_via_flat_cutoffs {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (hcoarea_integral : WeakRadialCoareaIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity_via_split_ingredients
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad
    (radialVectorFieldContDiffForCutoffs_of_constNearOrigin
      (n := n) (R0 := R0) hflat)
    hcoarea_integral hdefect_loc hibp_formula hprimitive

/-- Same route with the coarea ingredient supplied as the two standard radius
integral formulas for energy and radial energy.
@isnad1 id=weakboun.7h4v.s7.91be876af87a from=translated src=- shape=848198f7 vocab=844348bd
-/
theorem weak_boundary_identity_from_radial_identity_via_radius_formulas {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_radial_identity_via_flat_cutoffs
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad hflat
    (weakRadialCoareaIntegralFormula_of_radiusIntegral
      (n := n) (m := m) (Du := Du) (R0 := R0)
      henergy_radius hradial_radius)
    hdefect_loc hibp_formula hprimitive

/-- Boundary identity from the `W^{1,2}_{loc}`-friendly scalar-cutoff radial
stationarity interface and the split analytic ingredients.
@isnad1 id=weakboun.6h4v.s7.6351ab04b35b from=translated src=- shape=0690b09a vocab=00a2d5da
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_radius_formulas {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  have hcoarea : WeakRadialCoareaIntegralFormula Du R0 :=
    weakRadialCoareaIntegralFormula_of_radiusIntegral
      (n := n) (m := m) (Du := Du) (R0 := R0)
      henergy_radius hradial_radius
  have hone : WeakRadialOneDimensionalIdentity Du R0 :=
    weakRadialOneDimensionalIdentity_of_scalar_cutoff_and_coarea
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad hcoarea
  have hsharp : WeakOneDimensionalSharpCutoffStep Du R0 :=
    weakOneDimensionalSharpCutoffStep_of_distribution
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hdefect_loc
      (weakOneDimensionalToDistributionStep_of_ibp_and_primitives
        (n := n) (m := m) (Du := Du) (R0 := R0)
      (weakOneDimensionalIBPStep_of_formula
        (n := n) (m := m) (Du := Du) (R0 := R0) hibp_formula)
      hprimitive)
  exact weakBoundaryIdentity_of_sharpCutoffLimit (hsharp hone)

/-- Boundary identity from the scalar-cutoff radial stationarity interface and
restricted-weight radius formulas.
@isnad1 id=weakboun.6h4v.s7.1661e76f34ff from=translated src=- shape=0690b09a vocab=a0bf849d
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_radius_formulasForWeights
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  have hone : WeakRadialOneDimensionalIdentity Du R0 :=
    weakRadialOneDimensionalIdentity_of_scalar_cutoff_and_radiusIntegralForWeights
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad henergy_radius hradial_radius
  have hsharp : WeakOneDimensionalSharpCutoffStep Du R0 :=
    weakOneDimensionalSharpCutoffStep_of_distribution
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hdefect_loc
      (weakOneDimensionalToDistributionStep_of_ibp_and_primitives
        (n := n) (m := m) (Du := Du) (R0 := R0)
      (weakOneDimensionalIBPStep_of_formula
        (n := n) (m := m) (Du := Du) (R0 := R0) hibp_formula)
      hprimitive)
  exact weakBoundaryIdentity_of_sharpCutoffLimit (hsharp hone)

/-- Same scalar-cutoff route, but with the old one-dimensional IBP and
primitive-family black boxes replaced by their concrete split ingredients.
@isnad1 id=weakboun.7h4v.s7.074fbb24ceac from=translated src=- shape=bec12cb3 vocab=ccfe382e
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredients
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (henergy_ibp : WeakBallEnergyIntegrationByPartsFormula Du R0)
    (hibp_int : WeakOneDimensionalIBPIntegrability Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_radius_formulas
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    (weakOneDimensionalIBPFormula_of_energyIBP
      (n := n) (m := m) (Du := Du) (R0 := R0)
      henergy_ibp hibp_int)
    (weakOneDimensionalPrimitiveTestFamily_of_realization
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hprimitive_realize)

/-- Same scalar-cutoff route, with restricted-weight radius formulas and the
one-dimensional IBP/primitive pieces in their concrete split form.
@isnad1 id=weakboun.7h4v.s7.2325743868b1 from=translated src=- shape=bec12cb3 vocab=fe2c7aba
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredientsForWeights
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (henergy_ibp : WeakBallEnergyIntegrationByPartsFormula Du R0)
    (hibp_int : WeakOneDimensionalIBPIntegrability Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_radius_formulasForWeights
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    (weakOneDimensionalIBPFormula_of_energyIBP
      (n := n) (m := m) (Du := Du) (R0 := R0)
      henergy_ibp hibp_int)
    (weakOneDimensionalPrimitiveTestFamily_of_realization
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hprimitive_realize)

/-- Same scalar-cutoff route, with the one-dimensional radius calculus bundled
as a single input.
@isnad1 id=weakboun.6h4v.s7.0d1e623616e5 from=translated src=- shape=97f52bb9 vocab=cb339324
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_energy_calculus
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredients
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    (weakBallEnergyIntegrationByPartsFormula_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    (weakOneDimensionalIBPIntegrability_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    hprimitive_realize

/-- Same scalar-cutoff route, with restricted-weight radius formulas and the
one-dimensional radius calculus bundled as a single input.
@isnad1 id=weakboun.6h4v.s7.eac7cdefa407 from=translated src=- shape=97f52bb9 vocab=c4ad6cea
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_energy_calculusForWeights
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredientsForWeights
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    (weakBallEnergyIntegrationByPartsFormula_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    (weakOneDimensionalIBPIntegrability_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    hprimitive_realize

/-- Boundary identity with both remaining one-dimensional pieces packaged: the
energy calculus is an input, while primitive cutoffs are constructed from
interval integrals and a smooth bump.
@isnad1 id=weakboun.5h4v.s7.fe93ba7b0227 from=translated src=- shape=6caab956 vocab=ac0627f7
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_calculus_constructed_primitive
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_energy_calculus
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    hcalc (weakPrimitiveCutoffRealization R0)

/-- Boundary identity from scalar-cutoff stationarity and absolute continuity
of the two radius energy functions.  The primitive cutoff is the constructed
interval-integral/smooth-bump one.
@isnad1 id=weakboun.6h4v.s7.b1742087cd15 from=translated src=- shape=e47117d4 vocab=435cb55b
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_radius_ac
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_calculus_constructed_primitive
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    (weakBallEnergyOneDimensionalCalculus_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hR0_nonneg hac)

/-- Boundary identity with the primitive-cutoff realization constructed from
the interval primitive and a smooth bump.
@isnad1 id=weakboun.6h4v.s7.c2578718b2e5 from=translated src=- shape=0690b09a vocab=290ff5b0
-/
theorem weak_boundary_identity_from_scalar_cutoff_identity_via_constructed_primitive
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (henergy_ibp : WeakBallEnergyIntegrationByPartsFormula Du R0)
    (hibp_int : WeakOneDimensionalIBPIntegrability Du R0) :
    WeakBoundaryIdentity Du (0 : Domain n) R0 := by
  exact weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredients
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius hdefect_loc
    henergy_ibp hibp_int (weakPrimitiveCutoffRealization R0)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
