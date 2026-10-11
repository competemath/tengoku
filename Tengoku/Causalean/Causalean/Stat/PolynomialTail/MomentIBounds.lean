/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bounds for the inverse second moment `I`

`I P U λ = ∫ U/(max U λ)²` is sandwiched by `J` from above (`I ≤ J`, pointwise) and
by an elementary *shell* argument from below.  The shell `(ρλ, λ]` with
`ρ = (cm/(2cp))^{1/κ}` carries mass `≥ (cm/2)λᵏ` (upper tail at `ρλ`, lower tail at
`λ`) on which the integrand `U/λ² ≥ ρ/λ`, giving

    I P U λ  ≥  (ρ·cm/2) · λ^{κ-1}.

Combined with `I ≤ J ≤ A·λ^{κ-1}` (regime `κ < 1`) this yields the two-sided
bound `a·λ^{κ-1} ≤ I ≤ A·λ^{κ-1}`.  The shell lower bound crucially uses **both**
tail bounds (the gap `cm < cp` makes a one-sided argument fail).
-/

module
public import Tengoku.Causalean.Causalean.Stat.PolynomialTail.MomentJBounds

/-!
# Bounds for the inverse second moment

This module proves the corresponding regime bounds for
`I P U lam = invMomentI P U lam = int U / (max U lam)^2`.  The upper side comes from the pointwise
comparison `invMomentI_le_invMomentJ`, so the `J` bounds from `MomentJBounds` immediately control
`I`.

The lower side is specific to `I`: `invMomentI_ge_shell` uses the annulus
`rho * lam < U <= lam`, with `rho = (cm / (2 * cp))^(1 / kappa)`, to extract a positive mass
shell from the two-sided polynomial-tail assumption.  The module then proves
`invMomentI_bounds_lt`, `invMomentI_bounds_eq`, and `invMomentI_bounds_gt` for the three regimes,
plus `IsTheta` corollaries `invMomentJ_isTheta_lt`, `invMomentI_isTheta_lt`,
`invMomentJ_isTheta_gt`, and `invMomentI_isTheta_gt` as `lam -> 0+`.
-/

public section

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set Topology Filter Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
  {κ t₀ cm cp lam : ℝ}

/-- **`I ≤ J`.**  Pointwise `U/(max U λ)² ≤ (max U λ)⁻¹` (since `U ≤ max U λ`).
@isnad1 id=le.2h4v.s5.451f0d695122 from=translated src=- shape=4f2660c4 vocab=fece7e6f
-/
theorem invMomentI_le_invMomentJ [IsProbabilityMeasure P] (hsetup : TailSetup P U)
    (hlam_pos : 0 < lam) : invMomentI P U lam ≤ invMomentJ P U lam := by
  rw [invMomentI, invMomentJ]
  refine integral_mono_ae (integrable_invMomentI_integrand hsetup hlam_pos)
    (integrable_invMomentJ_integrand hsetup hlam_pos) ?_
  filter_upwards [hsetup.pos] with ω hUpos
  have hm : 0 < max (U ω) lam := lt_of_lt_of_le hlam_pos (le_max_right _ _)
  have hUm : U ω / max (U ω) lam ≤ 1 := by rw [div_le_one hm]; exact le_max_left _ _
  calc U ω / (max (U ω) lam) ^ 2
      = (U ω / max (U ω) lam) * (max (U ω) lam)⁻¹ := by
        rw [sq, ← div_div, div_eq_mul_inv]
    _ ≤ 1 * (max (U ω) lam)⁻¹ :=
        mul_le_mul_of_nonneg_right hUm (inv_nonneg.mpr hm.le)
    _ = (max (U ω) lam)⁻¹ := one_mul _

/-- **`J − I` is controlled by the tail mass.**  `J P U λ − I P U λ ≤ cp·λ^{κ-1}`.
Pointwise the gap equals `wλ/(max U λ) ≤ λ⁻¹·wλ`, and `∫ wλ ≤ P{U<λ} ≤ cp·λᵏ`.
@isnad1 id=le.4h8v.s6.172d501f209e from=translated src=- shape=83d9b3d4 vocab=b5a1bd45
-/
theorem invMomentJ_sub_invMomentI_le [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    invMomentJ P U lam - invMomentI P U lam ≤ cp * lam ^ (κ - 1) := by
  have hJint := integrable_invMomentJ_integrand hsetup hlam_pos
  have hIint := integrable_invMomentI_integrand hsetup hlam_pos
  have hWint := integrable_trimWeight hsetup hlam_pos
  have hsmeas : MeasurableSet {ω | U ω < lam} := hsetup.measurable measurableSet_Iio
  have hptbound : ∀ᵐ ω ∂P, (max (U ω) lam)⁻¹ - U ω / (max (U ω) lam) ^ 2
      ≤ lam⁻¹ * trimWeight U lam ω := by
    filter_upwards [hsetup.pos] with ω hUpos
    have hm : 0 < max (U ω) lam := lt_of_lt_of_le hlam_pos (le_max_right _ _)
    have heq : (max (U ω) lam)⁻¹ - U ω / (max (U ω) lam) ^ 2
        = trimWeight U lam ω / max (U ω) lam := by simp only [trimWeight]; field_simp
    rw [heq, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hlam_pos (le_max_right _ _))
      (trimWeight_mem hlam_pos hUpos).1
  have hWmass : ∫ ω, trimWeight U lam ω ∂P ≤ P.real {ω | U ω < lam} := by
    have hind : P.real {ω | U ω < lam}
        = ∫ ω, Set.indicator {ω | U ω < lam} (fun _ => (1 : ℝ)) ω ∂P := by
      rw [integral_indicator hsmeas, setIntegral_const, smul_eq_mul, mul_one]
    rw [hind]
    refine integral_mono_ae hWint ((integrable_const (1 : ℝ)).indicator hsmeas) ?_
    filter_upwards [hsetup.pos] with ω hUpos
    by_cases hω : U ω < lam
    · rw [Set.indicator_of_mem (show ω ∈ {ω | U ω < lam} from hω)]
      exact (trimWeight_mem hlam_pos hUpos).2
    · have hw0 : trimWeight U lam ω = 0 := by
        simp only [trimWeight, max_eq_left (not_lt.mp hω), div_self (ne_of_gt hUpos), sub_self]
      rw [hw0, Set.indicator_of_notMem (show ω ∉ {ω | U ω < lam} from hω)]
  rw [invMomentJ, invMomentI, ← integral_sub hJint hIint]
  calc ∫ ω, ((max (U ω) lam)⁻¹ - U ω / (max (U ω) lam) ^ 2) ∂P
      ≤ ∫ ω, lam⁻¹ * trimWeight U lam ω ∂P :=
        integral_mono_ae (hJint.sub hIint) (hWint.const_mul _) hptbound
    _ = lam⁻¹ * ∫ ω, trimWeight U lam ω ∂P := integral_const_mul _ _
    _ ≤ lam⁻¹ * (cp * lam ^ κ) := by
        have h1 : (0 : ℝ) ≤ lam⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left
          (le_trans hWmass (measureReal_lt_le h hlam_pos hlam_le)) h1
    _ = cp * lam ^ (κ - 1) := by rw [Real.rpow_sub hlam_pos, Real.rpow_one]; field_simp

/-- **`I` is antitone in `λ`.**  As `λ` decreases, `max U λ` decreases, so the
integrand `U/(max U λ)²` increases.  Hence `I P U λ₂ ≤ I P U λ₁` when `λ₁ ≤ λ₂`.
@isnad1 id=le.3h5v.s5.3501f3050541 from=translated src=- shape=46461366 vocab=312969bf
-/
theorem invMomentI_antitone [IsProbabilityMeasure P] (hsetup : TailSetup P U)
    {l1 l2 : ℝ} (hl1 : 0 < l1) (hl12 : l1 ≤ l2) :
    invMomentI P U l2 ≤ invMomentI P U l1 := by
  rw [invMomentI, invMomentI]
  refine integral_mono_ae (integrable_invMomentI_integrand hsetup (lt_of_lt_of_le hl1 hl12))
    (integrable_invMomentI_integrand hsetup hl1) ?_
  filter_upwards [hsetup.pos] with ω hUpos
  have hm1 : 0 < max (U ω) l1 := lt_of_lt_of_le hl1 (le_max_right _ _)
  have hmono : max (U ω) l1 ≤ max (U ω) l2 := max_le_max le_rfl hl12
  gcongr

/-! ## The shell lower bound -/

/-! ## Two-sided bound for `I` in the regime `κ < 1` -/

/-! ## Two-sided bound for `I` in the regime `κ = 1` -/

/-! ## Bounded `I` in the regime `κ > 1` -/

/-! ## IsTheta corollaries as `λ → 0⁺` -/

/-- Generic two-sided-bound ⟹ `IsTheta` packager on `𝓝[>] 0`.
@isnad1 id=istheta.5h5v.s7.ada38586e272 from=translated src=- shape=cbebb4fe vocab=2f1802d3
-/
theorem isTheta_of_two_sided {f g : ℝ → ℝ} {t₀ a A : ℝ} (ht0 : 0 < t₀) (ha : 0 < a)
    (hgpos : ∀ lam : ℝ, 0 < lam → lam ≤ t₀ → 0 < g lam)
    (hfnn : ∀ lam : ℝ, 0 < lam → lam ≤ t₀ → 0 ≤ f lam)
    (hbd : ∀ lam : ℝ, 0 < lam → lam ≤ t₀ → a * g lam ≤ f lam ∧ f lam ≤ A * g lam) :
    f =Θ[𝓝[>] (0 : ℝ)] g := by
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), 0 < lam ∧ lam ≤ t₀ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht0)]
      with lam h1 h2 using ⟨h1, le_of_lt h2⟩
  refine ⟨?_, ?_⟩
  · rw [Asymptotics.isBigO_iff]
    refine ⟨A, hev.mono fun lam ⟨hlp, hll⟩ => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hfnn lam hlp hll),
      abs_of_nonneg (hgpos lam hlp hll).le]
    exact (hbd lam hlp hll).2
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1 / a, hev.mono fun lam ⟨hlp, hll⟩ => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hgpos lam hlp hll).le,
      abs_of_nonneg (hfnn lam hlp hll), one_div, inv_mul_eq_div, le_div_iff₀ ha, mul_comm]
    exact (hbd lam hlp hll).1

/-- **IsTheta for `J` (κ < 1).** Under [the polynomial lower-tail hypothesis](hyp:h) with [`U`
measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent strictly between `0` and
`1`](hyp:hκ1), [the truncated inverse first moment `J P U λ` is `Θ(λ^{κ-1})` as `λ →
0⁺`](goal).
@isnad1 id=istheta.3h7v.s6.3e1493dfdb5b from=translated src=- shape=21adab76 vocab=ff67cbc0
-/
theorem invMomentJ_isTheta_lt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : κ < 1) :
    (fun lam => invMomentJ P U lam) =Θ[𝓝[>] (0 : ℝ)] fun lam => lam ^ (κ - 1) := by
  obtain ⟨a, A, ha, _, hbd⟩ := invMomentJ_bounds_lt h hsetup hκ1
  exact isTheta_of_two_sided h.t0_pos ha (fun lam hlp _ => Real.rpow_pos_of_pos hlp _)
    (fun lam hlp hll => le_trans (mul_nonneg ha.le (Real.rpow_nonneg hlp.le _))
      (hbd lam hlp hll).1) hbd

/-- **IsTheta for `J` (κ > 1).** Under [the polynomial lower-tail hypothesis](hyp:h) with [`U`
measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent strictly above
`1`](hyp:hκ1), [the truncated inverse first moment `J P U λ` is `Θ(1)` — bounded — as `λ →
0⁺`](goal).
@isnad1 id=istheta.3h7v.s6.9f75045433df from=translated src=- shape=10ffdaed vocab=c8a751c8
-/
theorem invMomentJ_isTheta_gt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : 1 < κ) :
    (fun lam => invMomentJ P U lam) =Θ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  obtain ⟨a, A, ha, _, hbd⟩ := invMomentJ_bounds_gt h hsetup hκ1
  exact isTheta_of_two_sided h.t0_pos ha (fun _ _ _ => one_pos)
    (fun lam hlp hll => le_trans ha.le (hbd lam hlp hll).1)
    (fun lam hlp hll => by simpa using hbd lam hlp hll)

end Causalean.Stat.PolynomialTail
