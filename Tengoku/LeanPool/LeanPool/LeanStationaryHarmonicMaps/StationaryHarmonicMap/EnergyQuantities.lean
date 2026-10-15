/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialGeometry

/-!
# Energy Quantities
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Energy on a ball. -/
def ballEnergy {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, energyDensity u x

/-- Radial energy on a ball. -/
def ballRadialEnergy {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, radialEnergyDensity u a x

/-- Weak energy on a ball, written in terms of the chosen weak gradient. -/
def weakBallEnergy {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, weakEnergyDensity Du x

/-- Weak radial energy on a ball, written in terms of the chosen weak gradient. -/
def weakBallRadialEnergy {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, weakRadialEnergyDensity Du a x

/-- The open ball of radius `0` is empty, so its weak energy is zero.
@isnad1 id=eq.0h4v.s5.b2498a1062c0 from=translated src=- shape=8b3b4a43 vocab=4dfc0c68
-/
theorem weakBallEnergy_zero_radius {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) :
    weakBallEnergy Du a 0 = 0 := by
  simp [weakBallEnergy, Metric.ball_eq_empty.mpr le_rfl]

/-- The open ball of radius `0` is empty, so its weak radial energy is zero.
@isnad1 id=eq.0h4v.s5.acbdebda5b9f from=translated src=- shape=8b3b4a43 vocab=df4a0f00
-/
theorem weakBallRadialEnergy_zero_radius {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) :
    weakBallRadialEnergy Du a 0 = 0 := by
  simp [weakBallRadialEnergy, Metric.ball_eq_empty.mpr le_rfl]

/-- The factor `r^(2-n)` as an integer power. -/
def thetaFactor (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (2 - (n : ℤ))

/-- The monotonicity factor is continuous on any closed interval bounded away
from the origin.
@isnad1 id=continuo.1h3v.s5.d2cabb1108e6 from=translated src=- shape=81673f16 vocab=7e650ad6
-/
theorem thetaFactor_continuousOn_Icc {n : ℕ} {s r : ℝ}
    (hs : 0 < s) :
    ContinuousOn (thetaFactor n) (Icc s r) := by
  have hnonzero :
      ∀ z ∈ Icc s r, (id z : ℝ) ≠ 0 ∨ 0 ≤ 2 - (n : ℤ) := by
    intro z hz
    exact Or.inl (ne_of_gt (hs.trans_le hz.1))
  exact continuous_id.continuousOn.zpow₀ (2 - (n : ℤ)) hnonzero

/-- The monotonicity quantity `Theta_u(a,r)`. -/
def theta {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (r : ℝ) : ℝ :=
  thetaFactor n r * ballEnergy u a r

/-- Weak monotonicity quantity, using the weak gradient energy. -/
def weakTheta {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) : ℝ :=
  thetaFactor n r * weakBallEnergy Du a r

/-- The factor `r^(2-n)` is smooth, hence absolutely continuous, on every
strictly positive radius interval.
@isnad1 id=absolute.2h3v.s4.5bed1f2e4c42 from=translated src=- shape=c249e712 vocab=f1fdee7f
-/
theorem thetaFactor_absolutelyContinuousOnInterval {n : ℕ} {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) :
    AbsolutelyContinuousOnInterval (thetaFactor n) s r := by
  have hsr_le : s ≤ r := le_of_lt hsr
  have hnonzero : ∀ z ∈ uIcc s r, (id z : ℝ) ≠ 0 := by
    intro z hz
    have hzIcc : z ∈ Icc s r := by
      simpa [uIcc_of_le hsr_le] using hz
    have hzs : s ≤ z := by
      exact hzIcc.1
    exact ne_of_gt (hs.trans_le hzs)
  have han :
      AnalyticOnNhd ℝ (fun z : ℝ => z ^ (2 - (n : ℤ))) (uIcc s r) :=
    (analyticOnNhd_id (𝕜 := ℝ) (E := ℝ) (s := uIcc s r)).zpow hnonzero
  have hud : UniqueDiffOn ℝ (uIcc s r) := by
    rw [uIcc_of_le hsr_le]
    exact uniqueDiffOn_Icc hsr
  have hcontdiff : ContDiffOn ℝ 1 (thetaFactor n) (uIcc s r) := by
    exact han.contDiffOn (n := (1 : ℕ∞)) hud
  exact hcontdiff.absolutelyContinuousOnInterval

/-- Derivative of the monotonicity weight.
@isnad1 id=eq.0h2v.s6.bde4e7146ba5 from=translated src=- shape=9d380bbc vocab=66c902be
-/
theorem deriv_thetaFactor {n : ℕ} {rho : ℝ} :
    deriv (thetaFactor n) rho =
      ((2 : ℝ) - (n : ℝ)) * rho ^ (1 - (n : ℤ)) := by
  have hcast : (((2 - (n : ℤ) : ℤ) : ℝ)) = (2 : ℝ) - (n : ℝ) := by
    norm_num
  have hexp : (2 - (n : ℤ) : ℤ) - 1 = 1 - (n : ℤ) := by
    omega
  unfold thetaFactor
  rw [deriv_zpow, hcast, hexp]

/-- Pointwise algebra turning the boundary identity into the derivative of the
monotonicity quantity.
@isnad1 id=eq.2h5v.s7.66d70e01517e from=translated src=- shape=eb1a4834 vocab=979b4ce1
-/
theorem thetaFactor_boundary_algebra {n : ℕ} {rho E E' Q' : ℝ}
    (hrho : rho ≠ 0)
    (hboundary : rho * E' - ((n : ℝ) - 2) * E = 2 * rho * Q') :
    deriv (thetaFactor n) rho * E + thetaFactor n rho * E' =
      2 * thetaFactor n rho * Q' := by
  have hpow :
      rho ^ (2 - (n : ℤ)) = rho ^ (1 - (n : ℤ)) * rho := by
    symm
    calc
      rho ^ (1 - (n : ℤ)) * rho =
          rho ^ (1 - (n : ℤ)) * rho ^ (1 : ℤ) := by
            rw [zpow_one]
      _ = rho ^ ((1 - (n : ℤ)) + (1 : ℤ)) := by
            rw [← zpow_add₀ hrho]
      _ = rho ^ (2 - (n : ℤ)) := by
            congr 1
            omega
  rw [deriv_thetaFactor (n := n), thetaFactor, hpow]
  have hscaled :=
    congrArg (fun t : ℝ => rho ^ (1 - (n : ℤ)) * t) hboundary
  nlinarith [hscaled]

/-- The annular weight `|x-a|^(2-n)`. -/
def annulusWeight (n : ℕ) (a x : Domain n) : ℝ :=
  ‖x - a‖ ^ (2 - (n : ℤ))

/-- Right-hand side of the monotonicity formula on `B_r(a) \ B_s(a)`. -/
def monotonicityRhs {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (s r : ℝ) : ℝ :=
  2 * ∫ x in Metric.ball a r \ Metric.ball a s,
    annulusWeight n a x * radialEnergyDensity u a x

/-- Right-hand side of the weak monotonicity formula on `B_r(a) \ B_s(a)`. -/
def weakMonotonicityRhs {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (s r : ℝ) : ℝ :=
  2 * ∫ x in Metric.ball a r \ Metric.ball a s,
    ‖x - a‖ ^ (2 - (n : ℤ)) * weakRadialEnergyDensity Du a x

/-- The weak annular radial-energy term is nonnegative.
@isnad1 id=le.0h6v.s5.aa003ab2467e from=translated src=- shape=d311bca1 vocab=484fe436
-/
theorem weakMonotonicityRhs_nonneg {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (s r : ℝ) :
    0 ≤ weakMonotonicityRhs Du a s r := by
  unfold weakMonotonicityRhs weakRadialEnergyDensity
  exact mul_nonneg zero_le_two
    (setIntegral_nonneg
      ((Metric.isOpen_ball : IsOpen (Metric.ball a r)).measurableSet.diff
        (Metric.isOpen_ball : IsOpen (Metric.ball a s)).measurableSet)
      (fun x _hx =>
        mul_nonneg (zpow_nonneg (norm_nonneg (x - a)) _)
          (sq_nonneg ‖weakRadialDerivative Du a x‖)))

/-- Coefficient multiplying the weak energy density in the radial identity. -/
def weakRadialMainCoeff (n : ℕ) (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  ((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖

/-- Coefficient multiplying the weak radial-energy density in the radial identity. -/
def weakRadialRhsCoeff {n : ℕ} (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  ‖x‖ * deriv phi ‖x‖

/-- Continuity of the main radial cutoff coefficient, assuming `phi` and `phi'`
are continuous.
@isnad1 id=continuo.2h2v.s6.d2b7f4d87601 from=translated src=- shape=d245af48 vocab=79a23449
-/
theorem weakRadialMainCoeff_continuous {n : ℕ} {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hdphi : Continuous (deriv phi)) :
    Continuous (fun x : Domain n => weakRadialMainCoeff n phi x) := by
  unfold weakRadialMainCoeff
  fun_prop

/-- Continuity of the radial-energy cutoff coefficient, assuming `phi'` is continuous.
@isnad1 id=continuo.1h2v.s6.cae19711cd9e from=translated src=- shape=9a62aa39 vocab=fcaa801a
-/
theorem weakRadialRhsCoeff_continuous {n : ℕ} {phi : ℝ → ℝ}
    (hdphi : Continuous (deriv phi)) :
    Continuous (fun x : Domain n => weakRadialRhsCoeff phi x) := by
  unfold weakRadialRhsCoeff
  fun_prop

/-- A `C¹` scalar cutoff gives a continuous main radial coefficient.
@isnad1 id=continuo.1h2v.s6.266a1b057a18 from=translated src=- shape=9653a381 vocab=3eb7e010
-/
theorem weakRadialMainCoeff_continuous_of_contDiff {n : ℕ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    Continuous (fun x : Domain n => weakRadialMainCoeff n phi x) :=
  weakRadialMainCoeff_continuous
    (n := n) (phi := phi) hphi.continuous hphi.continuous_deriv_one

/-- A `C¹` scalar cutoff gives a continuous radial-energy coefficient.
@isnad1 id=continuo.1h2v.s6.0d487983f410 from=translated src=- shape=9653a381 vocab=f3fa0dac
-/
theorem weakRadialRhsCoeff_continuous_of_contDiff {n : ℕ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    Continuous (fun x : Domain n => weakRadialRhsCoeff phi x) :=
  weakRadialRhsCoeff_continuous
    (n := n) (phi := phi) hphi.continuous_deriv_one

/-- The main radial cutoff coefficient is a.e. strongly measurable on any set.
@isnad1 id=aestrong.2h3v.s8.7d8ef35abb13 from=translated src=- shape=bc9dd502 vocab=cb2bf57c
-/
theorem weakRadialMainCoeff_aestronglyMeasurable {n : ℕ} {Ω : Set (Domain n)}
    {phi : ℝ → ℝ} (hphi : Continuous phi) (hdphi : Continuous (deriv phi)) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
      (volume.restrict Ω) :=
  (weakRadialMainCoeff_continuous (n := n) (phi := phi) hphi hdphi).aestronglyMeasurable

/-- The radial-energy cutoff coefficient is a.e. strongly measurable on any set.
@isnad1 id=aestrong.1h3v.s8.c7d4dd6a69b1 from=translated src=- shape=76f1b988 vocab=a71e344f
-/
theorem weakRadialRhsCoeff_aestronglyMeasurable {n : ℕ} {Ω : Set (Domain n)}
    {phi : ℝ → ℝ} (hdphi : Continuous (deriv phi)) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
      (volume.restrict Ω) :=
  (weakRadialRhsCoeff_continuous (n := n) (phi := phi) hdphi).aestronglyMeasurable

/-- The main radial cutoff coefficient is a.e. strongly measurable for a `C¹`
scalar cutoff.
@isnad1 id=aestrong.1h3v.s8.e6c9581bec80 from=translated src=- shape=adb07970 vocab=f593e19b
-/
theorem weakRadialMainCoeff_aestronglyMeasurable_of_contDiff {n : ℕ}
    {Ω : Set (Domain n)} {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
      (volume.restrict Ω) :=
  (weakRadialMainCoeff_continuous_of_contDiff (n := n) hphi).aestronglyMeasurable

/-- The radial-energy cutoff coefficient is a.e. strongly measurable for a `C¹`
scalar cutoff.
@isnad1 id=aestrong.1h3v.s8.91a5911c558d from=translated src=- shape=adb07970 vocab=17127ef0
-/
theorem weakRadialRhsCoeff_aestronglyMeasurable_of_contDiff {n : ℕ}
    {Ω : Set (Domain n)} {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
      (volume.restrict Ω) :=
  (weakRadialRhsCoeff_continuous_of_contDiff (n := n) hphi).aestronglyMeasurable

/-- If `phi` and `phi'` are bounded on `[0, R0]`, then the main radial coefficient
is a.e. bounded on `B_R0(0)`.
@isnad1 id=eventual.3h5v.s9.0eec3ce736a6 from=translated src=- shape=a88bbc87 vocab=27f306af
-/
theorem weakRadialMainCoeff_ae_bound_on_ball_of_radius_bounds {n : ℕ}
    {phi : ℝ → ℝ} {R0 M0 M1 : ℝ}
    (hphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖phi t‖ ≤ M0)
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
      ‖weakRadialMainCoeff n phi x‖ ≤ ‖((n : ℝ) - 2)‖ * M0 + R0 * M1 := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx_lt : ‖x‖ < R0 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hx_le : ‖x‖ ≤ R0 := le_of_lt hx_lt
  have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm₁ :
      ‖((n : ℝ) - 2) * phi ‖x‖‖ ≤ ‖((n : ℝ) - 2)‖ * M0 := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hphi_bound ‖x‖ hnorm_nonneg hx_le) (norm_nonneg _)
  have hterm₂ :
      ‖‖x‖ * deriv phi ‖x‖‖ ≤ R0 * M1 := by
    rw [norm_mul, Real.norm_of_nonneg hnorm_nonneg]
    exact mul_le_mul hx_le (hdphi_bound ‖x‖ hnorm_nonneg hx_le)
      (norm_nonneg _) hR0_nonneg
  have hsum :
      ‖((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖‖
        ≤ ‖((n : ℝ) - 2) * phi ‖x‖‖ + ‖‖x‖ * deriv phi ‖x‖‖ :=
    norm_add_le _ _
  calc
    ‖weakRadialMainCoeff n phi x‖
        = ‖((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖‖ := rfl
    _ ≤ ‖((n : ℝ) - 2) * phi ‖x‖‖ + ‖‖x‖ * deriv phi ‖x‖‖ := hsum
    _ ≤ ‖((n : ℝ) - 2)‖ * M0 + R0 * M1 := add_le_add hterm₁ hterm₂

/-- If `phi'` is bounded on `[0, R0]`, then the radial-energy coefficient is
a.e. bounded on `B_R0(0)`.
@isnad1 id=eventual.2h4v.s9.8cafd20f24ed from=translated src=- shape=f0646869 vocab=d61afa03
-/
theorem weakRadialRhsCoeff_ae_bound_on_ball_of_radius_bound {n : ℕ}
    {phi : ℝ → ℝ} {R0 M1 : ℝ}
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
      ‖weakRadialRhsCoeff phi x‖ ≤ R0 * M1 := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx_lt : ‖x‖ < R0 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hx_le : ‖x‖ ≤ R0 := le_of_lt hx_lt
  have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  calc
    ‖weakRadialRhsCoeff phi x‖
        = ‖‖x‖ * deriv phi ‖x‖‖ := rfl
    _ = ‖x‖ * ‖deriv phi ‖x‖‖ := by
          rw [norm_mul, Real.norm_of_nonneg hnorm_nonneg]
    _ ≤ R0 * M1 := by
          exact mul_le_mul hx_le (hdphi_bound ‖x‖ hnorm_nonneg hx_le)
            (norm_nonneg _) hR0_nonneg

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
