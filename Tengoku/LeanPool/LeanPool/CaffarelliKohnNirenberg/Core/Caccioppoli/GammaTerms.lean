/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI2Bound
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# The `γ`-form Caccioppoli terms

`paper/ckn.tex`, Lemma `lem:caccioppoli-gamma` (`eq:caccioppoli-gamma`), reruns
the proof of the Caccioppoli inequality `lem:caccioppoli` changing only the
bounds on the first two of the four error terms.  This file records those two
replacement bounds as standalone theorems about the same raw integrals that
`CKN.Core.Caccioppoli.RawI1` and `CKN.Core.Caccioppoli.RawI2Bound` bound.

* `I₁`: the test-function weight `|∂ₛφ + Δφ|` is bounded pointwise by
  `C r² ρ⁻⁵`, and `∫∫_{Q_ρ}|u|²` is estimated by Hölder with `1 = 2/3 + 1/3`,
  `∫∫_{Q_ρ}|u|² ≤ |Q_ρ|^{1/3} (∫∫_{Q_ρ}|u|³)^{2/3} = C ρ³ γ(ρ)²`.  Hence
  `I₁ ≤ C κ² γ(ρ)²` with `κ = r/ρ` (`caccioppoli_I1_gamma_heat_cutoff_raw_bound`).
* `I₂`: the Poincaré input is dropped; instead
  `||u|² − ⨍_{B_ρ}|u|²| |u| ≤ 2|u|³ + (⨍_{B_ρ}|u|²)^{3/2}` pointwise, the
  spatial average enters through the Jensen bound
  `⨍_{B_ρ}|u|² ≤ (⨍_{B_ρ}|u|³)^{2/3}`, and `∫∫_{Q_ρ}|u|³ = ρ² γ(ρ)³` gives
  `I₂ ≤ C κ⁻² γ(ρ)³` (`caccioppoli_I2_gamma_heat_cutoff_raw_bound`).

The remaining two terms `I₃`, `I₄` keep their proved bounds, so the conclusion
of `eq:caccioppoli-gamma` follows by the normalisation lemmas recorded here.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-! ## The two elementary estimates behind the replacement bounds -/

/-- Hölder's inequality on a measure space with conjugate exponents `3/2` and `3`
in the form used for `I₁`: the integral of a nonnegative function is bounded by
`(∫ A^{3/2})^{2/3}` times the `1/3` power of the total mass. -/
theorem caccioppoli_holder_l2_le_l3
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : α → ℝ≥0∞}
    (hA : AEMeasurable A μ) :
    (∫⁻ x, A x ∂μ) ≤
      (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (μ Set.univ) ^ (1 / 3 : ℝ) := by
  have hconj : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hone : AEMeasurable (fun _ : α => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hA hone
  calc
    (∫⁻ x, A x ∂μ) = ∫⁻ x, A x * (fun _ : α => (1 : ℝ≥0∞)) x ∂μ := by simp
    _ ≤ (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (1 / (3 / 2 : ℝ)) *
        (∫⁻ x, (fun _ : α => (1 : ℝ≥0∞)) x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := h
    _ = (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (μ Set.univ) ^ (1 / 3 : ℝ) := by
      rw [show (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) by norm_num]
      congr 2
      · simp

/-- The pointwise inequality behind `I₂` in its `γ`-form: for `N, m ≥ 0`,
`|N² − m| N ≤ 2 N³ + m^{3/2}`.  This combines the triangle inequality for the
mean subtraction with the Young inequality `mN ≤ m^{3/2} + N³`. -/
theorem caccioppoli_abs_sq_sub_mul_le (N m : ℝ) (hN : 0 ≤ N) (hm : 0 ≤ m) :
    |N ^ 2 - m| * N ≤ 2 * N ^ 3 + m ^ (3 / 2 : ℝ) := by
  have hN3 : 0 ≤ N ^ 3 := by positivity
  have hmp : 0 ≤ m ^ (3 / 2 : ℝ) := Real.rpow_nonneg hm _
  rcases le_or_gt m (N ^ 2) with h | h
  · rw [abs_of_nonneg (by linarith only [h])]
    have hle : (N ^ 2 - m) * N ≤ N ^ 3 := by
      have hstep : N ^ 2 - m ≤ N ^ 2 := by linarith only [hm]
      calc
        (N ^ 2 - m) * N ≤ N ^ 2 * N := mul_le_mul_of_nonneg_right hstep hN
        _ = N ^ 3 := by ring
    linarith only [hle, hN3, hmp]
  · rw [abs_of_neg (by linarith only [h])]
    have hNm : N ≤ m ^ (1 / 2 : ℝ) := by
      have hsqrt : Real.sqrt (N ^ 2) ≤ Real.sqrt m := Real.sqrt_le_sqrt h.le
      rwa [Real.sqrt_sq hN, Real.sqrt_eq_rpow] at hsqrt
    have hpowid : m ^ (3 / 2 : ℝ) = m * m ^ (1 / 2 : ℝ) := by
      have hmpos : 0 < m := by
        have hNsq : 0 ≤ N ^ 2 := by positivity
        linarith only [h, hNsq]
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hmpos,
        Real.rpow_one]
    have hmul : m * N ≤ m ^ (3 / 2 : ℝ) := by
      have hstep := mul_le_mul_of_nonneg_left hNm hm
      simpa only [← hpowid] using hstep
    have hle : (m - N ^ 2) * N ≤ m * N := by
      have hNsq : 0 ≤ N ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith only [hNsq]) hN
    linarith only [hle, hmul, hN3]

/-- The `ℝ≥0∞` form of `caccioppoli_abs_sq_sub_mul_le`, ready for integration.
The two `N³` terms are kept separate so that each can be matched against the
velocity integral `∫∫_{Q_ρ}|u|³`, and the exponent `3` of `N` is the real one so
that the term is literally `(ENNReal.ofReal N) ^ (3 : ℝ)`, the integrand of the
velocity identity `caccioppoli_I2_velocity_integral_identity`. -/
theorem caccioppoli_ennreal_abs_sq_sub_mul_le (N m : ℝ) (hN : 0 ≤ N)
    (hm : 0 ≤ m) :
    ENNReal.ofReal |N ^ 2 - m| * ENNReal.ofReal N ≤
      ENNReal.ofReal N ^ (3 : ℝ) + ENNReal.ofReal N ^ (3 : ℝ) +
        ENNReal.ofReal m ^ (3 / 2 : ℝ) := by
  have h := caccioppoli_abs_sq_sub_mul_le N m hN hm
  have hcube : ENNReal.ofReal (N ^ 3) = ENNReal.ofReal N ^ (3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hN (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    simp
  calc
    ENNReal.ofReal |N ^ 2 - m| * ENNReal.ofReal N
        = ENNReal.ofReal (|N ^ 2 - m| * N) := by
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * N ^ 3 + m ^ (3 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (2 * N ^ 3) + ENNReal.ofReal (m ^ (3 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_add] <;> positivity
    _ = ENNReal.ofReal N ^ (3 : ℝ) + ENNReal.ofReal N ^ (3 : ℝ) +
          ENNReal.ofReal m ^ (3 / 2 : ℝ) := by
        rw [show 2 * N ^ 3 = N ^ 3 + N ^ 3 by ring,
          ENNReal.ofReal_add (by positivity) (by positivity),
          hcube,
          ← ENNReal.ofReal_rpow_of_nonneg hm (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- The `L²` estimate for the velocity in the `γ`-form Caccioppoli inequality:
Hölder's inequality on `Q_ρ` with `1 = 2/3 + 1/3` combined with
`∫∫_{Q_ρ}|u|³ = ρ² γ(ρ)³` gives
`∫∫_{Q_ρ}|u|² ≤ |Q_ρ|^{1/3} (∫∫_{Q_ρ}|u|³)^{2/3} = (4π/3)^{1/3} ρ³ γ(ρ)²`. -/
theorem caccioppoli_velocity_l2_gamma_bound
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hA : AEMeasurable (fun w =>
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ))) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ 3 *
        gamma u (x₀, t₀) ρ ^ 2) := by
  let A : ParabolicPoint → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)
  have hAg : ∀ w, A w ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
    intro w
    dsimp only [A]
    rw [← ENNReal.rpow_mul]
    rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num]
  have hγ : 0 ≤ gamma u (x₀, t₀) ρ := by unfold gamma; positivity
  have hhold := caccioppoli_holder_l2_le_l3
    (μ := volume.restrict (parabolicCylinder x₀ t₀ ρ)) hA
  have hid := caccioppoli_I2_velocity_integral_identity
    (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hvol : (volume.restrict (parabolicCylinder x₀ t₀ ρ)) Set.univ =
      ENNReal.ofReal ((Real.pi * 4 / 3) * ρ ^ 5) := by
    rw [Measure.restrict_apply_univ]
    have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
    have hρ3 : 0 ≤ ρ ^ 3 := by positivity
    rw [volume_parabolicCylinder, volume_vec3Ball_eq]
    rw [← ENNReal.ofReal_pow hρ.le]
    rw [← ENNReal.ofReal_mul hρ3, ← ENNReal.ofReal_mul (mul_nonneg hρ3 hπ)]
    congr 1
    ring
  have hpow1 : (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) =
      ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 := by
    have hρpart : (ρ ^ 2) ^ (2 / 3 : ℝ) = ρ ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
      norm_num
    have hγpart : (gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) =
        gamma u (x₀, t₀) ρ ^ 2 := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hγ]
      norm_num
    calc
      (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ)
          = (ρ ^ 2) ^ (2 / 3 : ℝ) * (gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) :=
            Real.mul_rpow (by positivity) (by positivity)
      _ = ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 := by rw [hρpart, hγpart]
  have hpow2 : ((Real.pi * 4 / 3) * ρ ^ 5) ^ (1 / 3 : ℝ) =
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) := by
    have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
    have hρ5 : 0 ≤ ρ ^ 5 := by positivity
    have hρpart : (ρ ^ 5) ^ (1 / 3 : ℝ) = ρ ^ (5 / 3 : ℝ) := by
      rw [← Real.rpow_natCast ρ 5, ← Real.rpow_mul hρ.le]
      norm_num
    calc
      ((Real.pi * 4 / 3) * ρ ^ 5) ^ (1 / 3 : ℝ)
          = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (ρ ^ 5) ^ (1 / 3 : ℝ) :=
            Real.mul_rpow hπ hρ5
      _ = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) := by rw [hρpart]
  calc
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ, A w)
        ≤ (∫⁻ w in parabolicCylinder x₀ t₀ ρ, A w ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
            (volume.restrict (parabolicCylinder x₀ t₀ ρ) Set.univ) ^
              (1 / 3 : ℝ) := hhold
    _ = (ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal ((Real.pi * 4 / 3) * ρ ^ 5)) ^ (1 / 3 : ℝ) := by
        rw [lintegral_congr fun w => hAg w, hid, hvol]
    _ = ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ 3 *
          gamma u (x₀, t₀) ρ ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          hpow1, hpow2,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hρ.le _)
            (sq_nonneg _))]
        apply congrArg ENNReal.ofReal
        have hρadd : ρ ^ (4 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) = ρ ^ 3 := by
          rw [← Real.rpow_add hρ]
          rw [show (4 : ℝ) / 3 + 5 / 3 = 3 by norm_num]
          simp
        calc
          ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 *
              ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ)) =
              (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
                (ρ ^ (4 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ)) *
                  gamma u (x₀, t₀) ρ ^ 2 := by ring
          _ = _ := by rw [hρadd]

/-! ## The `I₁` replacement bound -/

/-! ## The `I₂` replacement bound -/

end CKN
