/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.MetricCodes.Binary
public import Tengoku

/-!
# Strict rate improvements

The MRRW comparison and the first spherical hierarchy and numerical bounds.
-/

@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace MRRW

section

open Filter Topology
open scoped Topology

theorem hasDerivAt_mul_continuous_zero
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hgzero : g 0 = 0) :
    HasDerivAt (fun r : ℝ => r * g r) 0 0 := by
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  have htend : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [hgzero] using hg.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hquotient :
      Tendsto (fun r : ℝ => r⁻¹ * (r * g r))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_congr' ?_).2 htend
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrzero : r ≠ 0 := by simpa only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff] using hr
    field_simp [hrzero]
  simpa only [zero_add, zero_mul, sub_zero, smul_eq_mul] using hquotient

/-- The smaller-branch inverse degree expression `(1 - sqrt (1 - r ^ 2)) / 2`. -/
def inverseDegree (r : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - r ^ 2)) / 2

/-- The reciprocal variance factor appearing in the inverse-degree entropy expansion. -/
def inverseVarianceFactor (r : ℝ) : ℝ :=
  (2 * (1 + Real.sqrt (1 - r ^ 2)))⁻¹

theorem inverseVarianceFactor_continuous :
    Continuous inverseVarianceFactor := by
  unfold inverseVarianceFactor
  apply Continuous.inv₀
  · fun_prop
  · intro r
    have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_nonneg _
    positivity

theorem inverseDegree_eq_sq_mul_factor
    {r : ℝ} (hr : r ^ 2 ≤ 1) :
    inverseDegree r = r * (r * inverseVarianceFactor r) := by
  have hradical : 0 ≤ 1 - r ^ 2 := by linarith
  have hsquare := Real.sq_sqrt hradical
  have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_nonneg _
  have hdenominator :
      1 + Real.sqrt (1 - r ^ 2) ≠ 0 := by
    positivity
  unfold inverseDegree inverseVarianceFactor
  field_simp [hdenominator]
  nlinarith

/-- The combination of negative logarithmic terms used in the inverse-degree entropy estimate. -/
def inverseEntropyFactor (r : ℝ) : ℝ :=
  inverseVarianceFactor r * Real.negMulLog r +
    Real.negMulLog (r * inverseVarianceFactor r)

theorem inverseEntropyFactor_continuous :
    Continuous inverseEntropyFactor := by
  unfold inverseEntropyFactor
  exact
    (inverseVarianceFactor_continuous.mul
      Real.continuous_negMulLog).add
      (Real.continuous_negMulLog.comp
        (continuous_id.mul inverseVarianceFactor_continuous))

@[simp] theorem inverseEntropyFactor_zero :
    inverseEntropyFactor 0 = 0 := by
  simp only [inverseEntropyFactor, inverseVarianceFactor, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_zero, Real.sqrt_one, mul_inv_rev, Real.negMulLog_zero,
    mul_zero, zero_mul, add_zero]

theorem negMulLog_inverseDegree_eventually :
    (fun r : ℝ => Real.negMulLog (inverseDegree r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => r * inverseEntropyFactor r) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 < 1 :=
    (continuousAt_id.pow 2).tendsto
      (gt_mem_nhds (by norm_num : (0 : ℝ) ^ 2 < 1))
  filter_upwards [hsmall] with r hr
  rw [inverseDegree_eq_sq_mul_factor hr.le,
    Real.negMulLog_mul]
  unfold inverseEntropyFactor
  ring

theorem hasDerivAt_negMulLog_inverseDegree_zero :
    HasDerivAt (fun r : ℝ => Real.negMulLog (inverseDegree r)) 0 0 := by
  exact
    (hasDerivAt_mul_continuous_zero inverseEntropyFactor
      inverseEntropyFactor_continuous.continuousAt
      inverseEntropyFactor_zero).congr_of_eventuallyEq
      negMulLog_inverseDegree_eventually

theorem hasDerivAt_inverseDegree_zero :
    HasDerivAt inverseDegree 0 0 := by
  have hradical :
      HasDerivAt (fun r : ℝ => 1 - r ^ 2) 0 0 := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_zero,
      mul_one, neg_zero] using ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub (1 : ℝ)
  have hroot :
      HasDerivAt (fun r : ℝ => Real.sqrt (1 - r ^ 2)) 0 0 := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Real.sqrt_one,
      mul_one, zero_div] using hradical.sqrt (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  unfold inverseDegree
  simpa only [Pi.sub_apply, sub_self, zero_div] using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hroot).div_const (2 : ℝ)

theorem hasDerivAt_mrrwG_sq_zero :
    HasDerivAt
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) 0 0 := by
  have hcomplement :
      HasDerivAt
        (fun r : ℝ => Real.negMulLog (1 - inverseDegree r)) 0 0 := by
    have hinner :
        HasDerivAt (fun r : ℝ => 1 - inverseDegree r) 0 0 := by
      change
        HasDerivAt
          ((fun _ : ℝ => (1 : ℝ)) - inverseDegree) 0 0
      simpa only [sub_self] using (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        hasDerivAt_inverseDegree_zero
    have houter :
        HasDerivAt Real.negMulLog (-1) (1 - inverseDegree 0) := by
      simpa only [inverseDegree, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
        Real.sqrt_one, sub_self, zero_div, Real.log_one, neg_zero,
        zero_sub] using Real.hasDerivAt_negMulLog (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Function.comp_def, mul_zero] using houter.comp 0 hinner
  have hentropy :
      HasDerivAt
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2)
        0 0 := by
    simpa only [Pi.add_apply, add_zero, zero_div] using
      (hasDerivAt_negMulLog_inverseDegree_zero.add hcomplement).div_const (Real.log 2)
  have hfunctions :
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) =
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2) := by
    funext r
    unfold MetricCodes.Johnson.mrrwG inverseDegree
    rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [hfunctions]
  exact hentropy

/-- The square-root term `sqrt (1 - 2 * δ)` in the MRRW lower-endpoint parameterization. -/
def lowerEndpointRoot (δ : ℝ) : ℝ :=
  Real.sqrt (1 - 2 * δ)

/-- The lower-endpoint weight `(1 - sqrt (1 - 2 * δ)) / 2`. -/
def lowerEndpointWeight (δ : ℝ) : ℝ :=
  (1 - lowerEndpointRoot δ) / 2

/-- The logarithmic derivative expression at the MRRW lower-endpoint weight. -/
def lowerEndpointDerivative (δ : ℝ) : ℝ :=
  δ *
    (Real.log (1 - lowerEndpointWeight δ) -
      Real.log (lowerEndpointWeight δ)) /
      (2 * lowerEndpointRoot δ * Real.log 2)

theorem lowerEndpointRoot_pos {δ : ℝ}
    (hhalf : δ < (1 : ℝ) / 2) :
    0 < lowerEndpointRoot δ := by
  unfold lowerEndpointRoot
  apply Real.sqrt_pos.mpr
  linarith

theorem lowerEndpointRoot_lt_one {δ : ℝ}
    (hδ : 0 < δ) :
    lowerEndpointRoot δ < 1 := by
  unfold lowerEndpointRoot
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
  linarith

theorem lowerEndpointWeight_pos {δ : ℝ}
    (hδ : 0 < δ) :
    0 < lowerEndpointWeight δ := by
  unfold lowerEndpointWeight
  linarith [lowerEndpointRoot_lt_one hδ]

theorem lowerEndpointWeight_lt_half {δ : ℝ}
    (hhalf : δ < (1 : ℝ) / 2) :
    lowerEndpointWeight δ < (1 : ℝ) / 2 := by
  unfold lowerEndpointWeight
  linarith [lowerEndpointRoot_pos hhalf]

theorem lowerEndpointDerivative_pos {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    0 < lowerEndpointDerivative δ := by
  have hweight := lowerEndpointWeight_pos hδ
  have hhalfweight := lowerEndpointWeight_lt_half hhalf
  have hlog :
      Real.log (lowerEndpointWeight δ) <
        Real.log (1 - lowerEndpointWeight δ) :=
    Real.log_lt_log hweight (by linarith)
  have hroot := lowerEndpointRoot_pos hhalf
  have hlogtwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  unfold lowerEndpointDerivative
  exact div_pos
    (mul_pos hδ (sub_pos.mpr hlog))
    (by positivity)

theorem hasDerivAt_mrrwG_boundary_quadratic_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ))
      (lowerEndpointDerivative δ) 0 := by
  have hquadratic :
      HasDerivAt
        (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ)
        (2 * δ) 0 := by
    simpa only [hasDerivAt_add_const_iff, id_eq, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
      Nat.add_one_sub_one,
      pow_one, mul_zero, mul_one, zero_add] using
      (((hasDerivAt_id (0 : ℝ)).pow 2).add ((hasDerivAt_id (0 : ℝ)).const_mul (2 *
        δ))).add_const (2 * δ)
  have hradical :
      HasDerivAt
        (fun r : ℝ =>
          1 - (r ^ 2 + 2 * δ * r + 2 * δ))
        (-2 * δ) 0 := by
    simpa only [neg_mul] using hquadratic.const_sub (1 : ℝ)
  have hradicalzero :
      1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ) ≠ 0 := by
    have hpositive : 0 < 1 - 2 * δ := by linarith
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      zero_add] using
      hpositive.ne'
  have hroot :
      HasDerivAt
        (fun r : ℝ =>
          Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)))
        ((-2 * δ) / (2 * lowerEndpointRoot δ)) 0 := by
    simpa only [neg_mul, lowerEndpointRoot, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero, zero_add] using hradical.sqrt hradicalzero
  have hnumerator :
      HasDerivAt
        ((fun _ : ℝ => (1 : ℝ)) -
          (fun r : ℝ =>
            Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ))))
        (0 - ((-2 * δ) / (2 * lowerEndpointRoot δ))) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hroot
  have hprobability :
      HasDerivAt
        (fun r : ℝ =>
          (1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2)
        (δ / (2 * lowerEndpointRoot δ)) 0 := by
    change
      HasDerivAt
        (fun r : ℝ =>
          (((fun _ : ℝ => (1 : ℝ)) -
            (fun s : ℝ =>
              Real.sqrt (1 - (s ^ 2 + 2 * δ * s + 2 * δ)))) r) /
            (2 : ℝ))
        (δ / (2 * lowerEndpointRoot δ)) 0
    exact
      (hnumerator.div_const (2 : ℝ)).congr_deriv (by ring)
  have hweight := lowerEndpointWeight_pos hδ
  have hweightone :
      lowerEndpointWeight δ ≠ 1 := by
    have h := lowerEndpointWeight_lt_half hhalf
    linarith
  have hentropyfun :
      MetricCodes.binaryEntropy =
        (fun a : ℝ => Real.binEntropy a / Real.log 2) :=
    funext MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log
  have hbinary :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        (lowerEndpointWeight δ) := by
    rw [hentropyfun]
    exact
      (Real.hasDerivAt_binEntropy hweight.ne'
        hweightone).div_const (Real.log 2)
  have hbinaryzero :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        ((1 - Real.sqrt
          (1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ))) / 2) := by
    simpa only [lowerEndpointWeight, lowerEndpointRoot, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add] using hbinary
  change
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.binaryEntropy
          ((1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2))
      (lowerEndpointDerivative δ) 0
  have hcoeff :
      ((Real.log (1 - lowerEndpointWeight δ) -
        Real.log (lowerEndpointWeight δ)) / Real.log 2) *
          (δ / (2 * lowerEndpointRoot δ)) =
        lowerEndpointDerivative δ := by
    unfold lowerEndpointDerivative
    field_simp [(lowerEndpointRoot_pos hhalf).ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  exact (hbinaryzero.comp 0 hprobability).congr_deriv hcoeff

theorem hasDerivAt_mrrwObjective_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt (MetricCodes.Johnson.mrrwObjective δ)
      (-lowerEndpointDerivative δ) 0 := by
  unfold MetricCodes.Johnson.mrrwObjective
  change
    HasDerivAt
      (((fun _ : ℝ => (1 : ℝ)) +
        (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2))) -
        (fun r : ℝ =>
          MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)))
      (-lowerEndpointDerivative δ) 0
  simpa only [add_zero, zero_sub] using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add hasDerivAt_mrrwG_sq_zero).sub
      (hasDerivAt_mrrwG_boundary_quadratic_zero hδ hhalf)

theorem exists_mrrwObjective_lt_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r < 1 - 2 * δ ∧
      MetricCodes.Johnson.mrrwObjective δ r <
        MetricCodes.Johnson.mrrwObjective δ 0 := by
  have hderivative := lowerEndpointDerivative_pos hδ hhalf
  have hslope :=
    (hasDerivAt_mrrwObjective_zero hδ hhalf).tendsto_slope_zero_right
  have hnegative :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        r⁻¹ *
          (MetricCodes.Johnson.mrrwObjective δ r -
            MetricCodes.Johnson.mrrwObjective δ 0) < 0 := by
    have h :=
      hslope.eventually
        (gt_mem_nhds (by linarith :
          -lowerEndpointDerivative δ < 0))
    filter_upwards [h] with r hr
    simpa only [zero_add, smul_eq_mul] using hr
  have hupper :
      ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 - 2 * δ :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - 2 * δ))
  have hwitness :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        0 < r ∧ r < 1 - 2 * δ ∧
          MetricCodes.Johnson.mrrwObjective δ r <
            MetricCodes.Johnson.mrrwObjective δ 0 := by
    filter_upwards [hnegative, hupper, self_mem_nhdsWithin]
      with r hquotient hrupper (hr : 0 < r)
    refine ⟨hr, hrupper, ?_⟩
    apply sub_neg.mp
    calc
      MetricCodes.Johnson.mrrwObjective δ r -
          MetricCodes.Johnson.mrrwObjective δ 0 =
        r *
          (r⁻¹ *
            (MetricCodes.Johnson.mrrwObjective δ r -
              MetricCodes.Johnson.mrrwObjective δ 0)) := by
          field_simp [hr.ne']
      _ < 0 := mul_neg_of_pos_of_neg hr hquotient
  exact hwitness.exists

theorem mrrw_minimizer_pos
    {δ r : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      MetricCodes.Johnson.mrrwObjective δ r ≤
        MetricCodes.Johnson.mrrwObjective δ s) :
    0 < r := by
  rcases hr.eq_or_lt with hzero | hpositive
  · have hrzero : r = 0 := hzero.symm
    subst r
    obtain ⟨s, hs, hsupper, hstrict⟩ :=
      exists_mrrwObjective_lt_zero hδ hhalf
    exact False.elim
      ((not_lt_of_ge (hmin s hs.le hsupper.le)) hstrict)
  · exact hpositive

theorem exists_positive_mrrw_minimizer
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 - 2 * δ ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        MetricCodes.Johnson.mrrwObjective δ r ≤
          MetricCodes.Johnson.mrrwObjective δ s) ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.mrrwObjective δ r := by
  obtain ⟨r, hr, hupper, hmin⟩ :=
    MetricCodes.Johnson.exists_mrrw_minimizer hhalf.le
  refine ⟨r, mrrw_minimizer_pos hδ hhalf hr hupper hmin,
    hupper, hmin, ?_⟩
  exact MetricCodes.Johnson.mrrwRate_eq_objective_of_minimizer
    hr hupper hmin

private def inverseWeight (δ r : ℝ) : ℝ :=
  (1 - Real.sqrt
    (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2

theorem inverse_zero_fibre_boundary
    {δ r : ℝ}
    (hδ : 0 < δ) (_ : δ < (1 : ℝ) / 2)
    (hr : 0 < r) (hupper : r < 1 - 2 * δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hrplus : 0 < 1 + r := by linarith
  have hrminus : 0 < 1 - r := by linarith
  have hmargin : 0 < 1 - 2 * δ - r := by linarith
  have hrvariance : 0 < 1 - r ^ 2 := by
    nlinarith only [mul_pos hrminus hrplus]
  have hquadratic :
      0 < 1 - (r ^ 2 + 2 * δ * r + 2 * δ) := by
    nlinarith only [mul_pos hrplus hmargin]
  have hradorder :
      1 - (r ^ 2 + 2 * δ * r + 2 * δ) <
        1 - r ^ 2 := by
    nlinarith only [mul_pos hδ hrplus]
  have hrootorder :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) <
        Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_lt_sqrt hquadratic.le hradorder
  have hrootlt : Real.sqrt (1 - r ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith only [mul_pos hr hr]
  have hsmallroot :
      0 < Real.sqrt
        (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) :=
    Real.sqrt_pos.mpr hquadratic
  have hdegreesquare :
      Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
    Real.sq_sqrt hrvariance.le
  have hweightsquare :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) ^ 2 =
        1 - (r ^ 2 + 2 * δ * r + 2 * δ) :=
    Real.sq_sqrt hquadratic.le
  let u : ℝ := inverseDegree r
  let a : ℝ := inverseWeight δ r
  have hu : 0 < u := by
    dsimp [u, inverseDegree]
    linarith
  have hua : u < a := by
    dsimp [u, a, inverseDegree, inverseWeight]
    linarith
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a, inverseWeight]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have haone : 0 < 1 - a := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvarianceu : 4 * u * (1 - u) = r ^ 2 := by
    dsimp [u, inverseDegree]
    nlinarith only [hdegreesquare]
  have hvariancea :
      4 * a * (1 - a) =
        r ^ 2 + 2 * δ * r + 2 * δ := by
    dsimp [a, inverseWeight]
    nlinarith only [hweightsquare]
  have hdistancevariance : 2 * δ < 4 * a * (1 - a) := by
    rw [hvariancea]
    nlinarith only [mul_pos hδ hr, sq_nonneg r]
  have hvarianceweight : 4 * a * (1 - a) < 4 * a := by
    nlinarith only [mul_pos ha0 ha0]
  have hweightdistance : δ / 2 < a := by
    nlinarith only [hdistancevariance, hvarianceweight]
  have husquare := Real.sq_sqrt (mul_pos hu huone).le
  have hrootsquare :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 = r ^ 2 := by
    nlinarith only [husquare, hvarianceu]
  have huradical :
      2 * Real.sqrt (u * (1 - u)) = r := by
    calc
      2 * Real.sqrt (u * (1 - u)) =
          Real.sqrt ((2 * Real.sqrt (u * (1 - u))) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (r ^ 2) := by rw [hrootsquare]
      _ = r := Real.sqrt_sq hr.le
  have hplus : 1 + r ≠ 0 := hrplus.ne'
  have hfraction :
      (a * (1 - a) - u * (1 - u)) /
        (a * (1 - a) * (1 + r)) =
        δ / (2 * a * (1 - a)) := by
    field_simp [ha0.ne', haone.ne', hplus];
      nlinarith only [hvariancea, hvarianceu]
  have hspectral :
      1 - MetricCodes.Johnson.spectralLimit a 0 0 u =
        (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + r)) := by
    simpa only [huradical] using
      MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  have hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a := by
    unfold MetricCodes.Johnson.asymptoticThreshold
    linarith only [hspectral, hfraction]
  have hobjective :
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
    simpa only [huradical] using
      MetricCodes.Johnson.mrrwObjective_zero_fibre_boundary
        hu hua ha hboundary
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hobjective⟩

theorem exists_zero_fibre_boundary_of_interior_minimizer
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ <
        MetricCodes.Hamming.classicalRate δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  obtain ⟨r, hr, hupper, _hmin, hrate⟩ :=
    exists_positive_mrrw_minimizer hδ hhalf
  have hrstrict : r < 1 - 2 * δ := by
    rcases lt_or_eq_of_le hupper with hlt | heq
    · exact hlt
    · exfalso
      have hendpoint :
          MetricCodes.Johnson.mrrwRate δ =
            MetricCodes.Hamming.classicalRate δ := by
        calc
          MetricCodes.Johnson.mrrwRate δ =
              MetricCodes.Johnson.mrrwObjective δ r := hrate
          _ = MetricCodes.Johnson.mrrwObjective δ (1 - 2 * δ) := by
            rw [heq]
          _ = MetricCodes.Hamming.classicalRate δ :=
            MetricCodes.Johnson.mrrwObjective_endpoint hδ hhalf
      exact (ne_of_lt hstrict) hendpoint
  obtain ⟨a, u, hu, hua, ha, hweightdistance,
      hboundary, hobjective⟩ :=
    inverse_zero_fibre_boundary hδ hhalf hr hrstrict
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hrate.trans hobjective⟩

end

section

open Filter Topology
open scoped Topology

/-- The reciprocal slope factor defining the interior perturbation of the shell weight. -/
def interiorSlope (a u : ℝ) : ℝ :=
  (Real.sqrt (u * (1 - u)) * (1 - 2 * a))⁻¹

/-- The shell weight perturbed linearly from `a` with the prescribed interior slope. -/
def interiorWeight (a u e : ℝ) : ℝ :=
  a - interiorSlope a u * e

/-- The support-degree parameter along the interior perturbation, equal to the weight times `e`. -/
def interiorSupport (a u e : ℝ) : ℝ :=
  interiorWeight a u e * e

/-- The complement-degree parameter along the interior perturbation, equal to the complement
weight times `e`. -/
def interiorComplement (a u e : ℝ) : ℝ :=
  (1 - interiorWeight a u e) * e

@[simp] theorem interiorWeight_zero (a u : ℝ) :
    interiorWeight a u 0 = a := by
  simp only [interiorWeight, mul_zero, sub_zero]

@[simp] theorem interiorSupport_zero (a u : ℝ) :
    interiorSupport a u 0 = 0 := by
  simp only [interiorSupport, interiorWeight_zero, mul_zero]

@[simp] theorem interiorComplement_zero (a u : ℝ) :
    interiorComplement a u 0 = 0 := by
  simp only [interiorComplement, interiorWeight_zero, mul_zero]

theorem interiorSupport_add_complement (a u e : ℝ) :
    interiorSupport a u e + interiorComplement a u e = e := by
  unfold interiorSupport interiorComplement
  ring

theorem rankPenalty_interior {a u e : ℝ}
    (hweight : 0 < interiorWeight a u e)
    (hweight' : interiorWeight a u e < 1) :
    MetricCodes.Johnson.rankPenalty
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) =
      MetricCodes.binaryEntropy e := by
  have hsupport :
      interiorSupport a u e / interiorWeight a u e = e := by
    unfold interiorSupport
    exact mul_div_cancel_left₀ e hweight.ne'
  have hcomplement :
      interiorComplement a u e / (1 - interiorWeight a u e) = e := by
    unfold interiorComplement
    exact mul_div_cancel_left₀ e (sub_pos.mpr hweight').ne'
  unfold MetricCodes.Johnson.rankPenalty
  rw [hsupport, hcomplement]
  ring

theorem tendsto_interiorWeight_zero (a u : ℝ) :
    Tendsto (interiorWeight a u) (𝓝[>] 0) (𝓝 a) := by
  have hcontinuous : Continuous (interiorWeight a u) := by
    unfold interiorWeight
    fun_prop
  simpa only [interiorWeight_zero] using
    hcontinuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

theorem eventually_binaryEntropy_inward_improvement
    {a : ℝ} (ha : 0 < a) (ha' : a < 1) (C : ℝ) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        MetricCodes.binaryEntropy e := by
  let f : ℝ → ℝ := fun e =>
    MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)
  have hinner :
      DifferentiableAt ℝ (fun e : ℝ => a - C * e) 0 := by
    fun_prop
  have houter : DifferentiableAt ℝ MetricCodes.binaryEntropy a :=
    MetricCodes.Hamming.differentiableAt_binaryEntropy ha ha'
  have houter0 :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (a - C * (0 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using houter
  have hf : DifferentiableAt ℝ f 0 := by
    dsimp [f]
    exact (houter0.comp 0 hinner).const_sub (MetricCodes.binaryEntropy a)
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ e : ℝ in 𝓝[>] 0,
        e⁻¹ *
          (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with e he
    simpa [f, smul_eq_mul] using he
  have hloglim :
      Tendsto (fun e : ℝ => -Real.logb 2 e) (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ e : ℝ in 𝓝[>] 0, M < -Real.logb 2 e :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with e hbound hlog' heone (he : 0 < e)
  have houter_bound :
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        e * M := by
    calc
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) =
          e * (e⁻¹ *
            (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e))) := by
            field_simp [he.ne']
      _ < e * M := mul_lt_mul_of_pos_left hbound he
  have hsingular : e * M < e * (-Real.logb 2 e) :=
    mul_lt_mul_of_pos_left hlog' he
  have hentropy :=
    MetricCodes.Hamming.neg_mul_logb_le_binaryEntropy he.le heone.le
  linarith

theorem eventually_shellRate_interior_improvement
    {a u : ℝ} (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hentropy := eventually_binaryEntropy_inward_improvement
    ha (ha'.trans (by norm_num)) (interiorSlope a u)
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds ha)
  have hless :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < 1 :=
    hweight.eventually
      (gt_mem_nhds (ha'.trans (by norm_num : (1 : ℝ) / 2 < 1)))
  filter_upwards [hentropy, hpositive, hless]
    with e he hpos hlt
  rw [MetricCodes.Johnson.shellRate, rankPenalty_interior hpos hlt,
    MetricCodes.Johnson.shellRate_zero_fibre]
  change
    1 - MetricCodes.binaryEntropy (a - interiorSlope a u * e) +
        MetricCodes.binaryEntropy u - MetricCodes.binaryEntropy e <
      1 - MetricCodes.binaryEntropy a + MetricCodes.binaryEntropy u
  linarith

/-- The perturbed Johnson spectral limit minus its asymptotic code-distance threshold. -/
def interiorSpectralMargin (δ a u e : ℝ) : ℝ :=
  MetricCodes.Johnson.spectralLimit
      (interiorWeight a u e)
      (interiorSupport a u e)
      (interiorComplement a u e) u -
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e)

theorem interiorSpectralMargin_zero {δ a u : ℝ}
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    interiorSpectralMargin δ a u 0 = 0 := by
  simp only [interiorSpectralMargin, interiorWeight_zero, interiorSupport_zero,
    interiorComplement_zero, hboundary, sub_self]

theorem interior_boundary_delta_relation {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ * (1 + 2 * Real.sqrt (u * (1 - u))) =
      2 * (a * (1 - a) - u * (1 - u)) := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  nlinarith

theorem interior_boundary_weight_gt_distance {δ a u : ℝ}
    (hδ : 0 < δ)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ / 2 < a := by
  have ha0 : 0 < a := lt_trans hu hua
  have huone : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu huone)
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  have hcross : 0 < δ * (2 * Real.sqrt (u * (1 - u))) := by
    positivity
  nlinarith [sq_nonneg (2 * Real.sqrt (u * (1 - u))),
    sq_pos_of_pos ha0]

theorem spectralLimit_interior_eq (a u e : ℝ) :
    MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u =
      let z := (1 - 2 * u)
      let m := (1 - 2 * (interiorWeight a u e))
      let t := 1 - 2 * e
      (m * (t ^ 2 - z ^ 2)) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - (m * t) ^ 2) * (t ^ 2 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) := by
  dsimp [MetricCodes.Johnson.spectralLimit,
    MetricCodes.Johnson.centeredEta,
    interiorSupport, interiorComplement]
  ring

theorem eventually_interior_parameters
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hδa : δ / 2 < a)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.AsymptoticParameters δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := tendsto_interiorWeight_zero a u
  have hweight_distance :
      ∀ᶠ e : ℝ in 𝓝[>] 0, δ / 2 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hδa)
  have hweight_half :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < (1 : ℝ) / 2 :=
    hweight.eventually (gt_mem_nhds ha)
  have hweight_degree :
      ∀ᶠ e : ℝ in 𝓝[>] 0, u < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hua)
  have hehalf : ∀ᶠ e : ℝ in 𝓝[>] 0, e < (1 : ℝ) / 2 :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hedegree : ∀ᶠ e : ℝ in 𝓝[>] 0, e < u :=
    nhdsWithin_le_nhds (gt_mem_nhds hu)
  have hleftcontinuous : Continuous
      (fun e : ℝ =>
        interiorWeight a u e - interiorSupport a u e +
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hleftlimit :
      Tendsto
        (fun e : ℝ =>
          interiorWeight a u e - interiorSupport a u e +
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 a) := by
    simpa only [interiorWeight_zero, interiorSupport_zero, sub_zero, interiorComplement_zero,
      add_zero] using
      hleftcontinuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hleft : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < interiorWeight a u e - interiorSupport a u e +
        interiorComplement a u e :=
    hleftlimit.eventually (lt_mem_nhds hua)
  have hrightcontinuous : Continuous
      (fun e : ℝ =>
        1 - interiorWeight a u e + interiorSupport a u e -
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hrightlimit :
      Tendsto
        (fun e : ℝ =>
          1 - interiorWeight a u e + interiorSupport a u e -
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 (1 - a)) := by
    simpa only [interiorWeight_zero, interiorSupport_zero, add_zero, interiorComplement_zero,
      sub_zero] using
      hrightcontinuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have huright : u < 1 - a := by linarith
  have hright : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < 1 - interiorWeight a u e + interiorSupport a u e -
        interiorComplement a u e :=
    hrightlimit.eventually (lt_mem_nhds huright)
  filter_upwards [hweight_distance, hweight_half, hweight_degree,
    hehalf, hedegree, hleft, hright, self_mem_nhdsWithin]
    with e hwd hwh hwu heh heu hel her (he : 0 < e)
  have hwpos : 0 < interiorWeight a u e := by
    nlinarith
  have hwcomplement : 0 < 1 - interiorWeight a u e := by
    linarith
  refine {
    distance_pos := hδ
    distance_lt_half := hδ'
    weight_gt_distance := hwd
    weight_lt_half := hwh
    support_nonneg := ?_
    support_lt_half := ?_
    complement_nonneg := ?_
    complement_lt_half := ?_
    first_lt_degree := ?_
    degree_lt_weight := hwu
    degree_lt_left := hel
    degree_lt_right := her
  }
  · unfold interiorSupport
    exact mul_nonneg hwpos.le he.le
  · unfold interiorSupport
    nlinarith [mul_lt_mul_of_pos_left heh hwpos]
  · unfold interiorComplement
    exact mul_nonneg hwcomplement.le he.le
  · unfold interiorComplement
    nlinarith [mul_lt_mul_of_pos_left heh hwcomplement]
  · rw [interiorSupport_add_complement]
    exact heu

theorem hasDerivAt_interiorSpectralMargin
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    HasDerivAt (interiorSpectralMargin δ a u)
      ((1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u))))) 0 := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hz0 : 0 < 1 - 2 * u := by linarith
  have hm0 : 0 < 1 - 2 * a := by linarith
  have hrad : 0 < 1 - (1 - 2 * u) ^ 2 := by
    nlinarith [mul_pos hu hu1]
  have hmrad : 0 < 1 - (1 - 2 * a) ^ 2 := by
    nlinarith [mul_pos ha0 ha1]
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hsquare := Real.sq_sqrt (mul_pos hu hu1).le
  have hroot :
      Real.sqrt (1 - (1 - 2 * u) ^ 2) =
        2 * Real.sqrt (u * (1 - u)) := by
    exact MetricCodes.Johnson.sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hdelta :=
    interior_boundary_delta_relation hu hua ha hboundary
  let c : ℝ := interiorSlope a u
  let A : ℝ → ℝ := fun e => a - c * e
  let m : ℝ → ℝ := fun e => 1 - 2 * A e
  let t : ℝ → ℝ := fun e => 1 - 2 * e
  let z : ℝ := 1 - 2 * u
  let q : ℝ := Real.sqrt (1 - z ^ 2)
  let p : ℝ → ℝ := fun e => t e ^ 2 - z ^ 2
  let Q : ℝ → ℝ := fun e => 1 - m e ^ 2
  have hA : HasDerivAt A (-c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => a) - (fun e : ℝ => c * e)) (-c) 0
    simpa only [id_eq, mul_one, zero_sub] using
      (hasDerivAt_const (x := (0 : ℝ)) a).sub ((hasDerivAt_id (0 : ℝ)).const_mul c)
  have hm : HasDerivAt m (2 * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          (fun e : ℝ => 2 * (a - c * e)))
        (2 * c) 0
    simpa only [mul_neg, sub_neg_eq_add, zero_add] using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub (hA.const_mul 2)
  have ht : HasDerivAt t (-2) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) - (fun e : ℝ => 2 * e))
        (-2) 0
    simpa only [id_eq, mul_one, zero_sub] using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have hp : HasDerivAt p (-4) 0 := by
    change
      HasDerivAt
        (((fun e : ℝ => 1 - 2 * e) ^ 2) -
          (fun _ : ℝ => z ^ 2))
        (-4) 0
    exact
      ((ht.pow 2).sub
        (hasDerivAt_const (x := (0 : ℝ)) (z ^ 2))).congr_deriv
        (by norm_num)
  have hQ : HasDerivAt Q (-4 * (1 - 2 * a) * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          ((fun e : ℝ => 1 - 2 * (a - c * e)) ^ 2))
        (-4 * (1 - 2 * a) * c) 0
    exact
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hm.pow 2)).congr_deriv (by dsimp [m, A]; ring)
  have hden1 : z ^ 2 * Q 0 * (1 - z ^ 2) ≠ 0 := by
    simpa [z, Q, m, A] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hrad.ne'
  have hden2 : z ^ 2 * Q 0 * q ≠ 0 := by
    have hroot_ne : Real.sqrt (1 - (1 - 2 * u) ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hrad).ne'
    simpa [z, Q, m, A, q] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hroot_ne
  have hden3 : 2 * A 0 * (1 - A 0) ≠ 0 := by
    simpa [A] using
      mul_ne_zero
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha0.ne')
        ha1.ne'
  have hterm1 :=
    ((hm.mul hp).pow 2).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) (1 - z ^ 2))) hden1
  have hterm2 :=
    (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).sub
        ((hm.mul ht).pow 2)).mul hp).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) q)) hden2
  have hthreshold :=
    (hasDerivAt_const (x := (0 : ℝ)) δ).div
      ((hA.const_mul 2).mul
        ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hA))
      hden3
  have hraw :=
    ((hterm1.add hterm2).sub
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ))).add hthreshold
  have hfun :
      (fun e : ℝ => interiorSpectralMargin δ a u e) =
        (fun e : ℝ =>
          (m e * p e) ^ 2 /
              (z ^ 2 * Q e * (1 - z ^ 2)) +
            ((z ^ 2 - (m e * t e) ^ 2) * p e) /
              (z ^ 2 * Q e * q) - 1 +
            δ / (2 * A e * (1 - A e))) := by
    funext e
    unfold interiorSpectralMargin
    rw [spectralLimit_interior_eq]
    dsimp [MetricCodes.Johnson.asymptoticThreshold,
      A, m, t, z, q, p, Q, c, interiorWeight]
    ring
  change HasDerivAt (fun e : ℝ => interiorSpectralMargin δ a u e) _ 0
  rw [hfun]
  refine hraw.congr_deriv ?_
  simp only [Nat.cast_ofNat, interiorSlope, mul_inv_rev, Pi.mul_apply, mul_zero, sub_zero, one_pow,
    Nat.add_one_sub_one, pow_one, mul_neg, Pi.pow_apply, zero_mul, neg_mul, zero_add, add_zero,
    sub_neg_eq_add, mul_one, zero_sub, Pi.sub_apply, m, A, c, p, t, z, Q, q]
  rw [hroot]
  have hdelta_div :
      δ =
        2 * (a * (1 - a) - u * (1 - u)) /
          (1 + 2 * Real.sqrt (u * (1 - u))) := by
    apply (eq_div_iff (by positivity)).2
    exact hdelta
  rw [hdelta_div]
  field_simp [ha0.ne', ha1.ne', hu.ne', hu1.ne',
    hz0.ne', hm0.ne', hs.ne', hrad.ne', hmrad.ne']
  ring_nf at hsquare ⊢
  linear_combination
    ((-128 * a ^ 3 * (a - 1) ^ 3 * (2 * a - 1) ^ 3 *
        Real.sqrt (u - u ^ 2)) +
      (64 * a ^ 2 * u * (a - 1) ^ 2 * (2 * a - 1) * (u - 1))) *
      hsquare

theorem interiorSpectralMargin_derivative_pos
    {a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    0 <
      (1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hvariance : u * (1 - u) < (1 : ℝ) / 4 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1 - 2 * u)]
  have hshalf : Real.sqrt (u * (1 - u)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by nlinarith)
  have hweight : 0 < 1 - 2 * (a * (1 - a)) := by
    nlinarith [sq_nonneg (a - (1 : ℝ) / 2)]
  exact div_pos
    (mul_pos hweight (by linarith))
    (by positivity)

theorem eventually_interiorSpectralMargin_pos
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSpectralMargin δ a u e := by
  have hderiv :=
    hasDerivAt_interiorSpectralMargin hu hua ha hboundary
  have hpositive := interiorSpectralMargin_derivative_pos hu hua ha
  have hslope := hderiv.tendsto_slope_zero_right
  have heventual := hslope.eventually (lt_mem_nhds hpositive)
  filter_upwards [heventual, self_mem_nhdsWithin]
    with e he (hepos : 0 < e)
  have hzero := interiorSpectralMargin_zero hboundary
  have hslopepos : 0 < e⁻¹ * interiorSpectralMargin δ a u e := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using he
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hepos)).mp hslopepos

theorem eventually_interior_feasible
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := interior_boundary_weight_gt_distance
    hδ hu hua ha hboundary
  have hparameters := eventually_interior_parameters
    hδ hδ' hweight hu hua ha
  have hspectral := eventually_interiorSpectralMargin_pos
    hu hua ha hboundary
  filter_upwards [hparameters, hspectral] with e he hs
  refine ⟨he, ?_⟩
  change
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e) <
      MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u
  exact sub_pos.mp hs

theorem interior_shell_improvement
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∃ A b g : ℝ,
      0 < b ∧ 0 < g ∧
      MetricCodes.Johnson.Feasible δ A b g u ∧
      MetricCodes.Johnson.shellRate A b g u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hfeasible := eventually_interior_feasible
    hδ hδ' hu hua ha hboundary
  have himprovement := eventually_shellRate_interior_improvement
    (u := u) (lt_trans hu hua) ha
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds (lt_trans hu hua))
  have hcomplement :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < 1 - interiorWeight a u e := by
    filter_upwards
      [hweight.eventually
        (gt_mem_nhds (show a < (1 : ℝ) by linarith))]
      with e he
    linarith
  have hall : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSupport a u e ∧
      0 < interiorComplement a u e ∧
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u ∧
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
    filter_upwards [hfeasible, himprovement, hpositive, hcomplement,
      self_mem_nhdsWithin] with e hf hi hw hc (he : 0 < e)
    refine ⟨?_, ?_, hf, hi⟩
    · unfold interiorSupport
      exact mul_pos hw he
    · unfold interiorComplement
      exact mul_pos hc he
  obtain ⟨e, he⟩ := hall.exists
  exact ⟨interiorWeight a u e,
    interiorSupport a u e, interiorComplement a u e, he⟩

theorem variationalRate_lt_mrrw_of_interior
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ < MetricCodes.Hamming.classicalRate δ) :
    MetricCodes.Johnson.variationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  obtain ⟨a, u, hu, hua, ha, _hweight, hboundary, hrate⟩ :=
    exists_zero_fibre_boundary_of_interior_minimizer
      hδ hhalf hstrict
  obtain ⟨A, b, g, _hb, _hg, hfeasible, himprovement⟩ :=
    interior_shell_improvement hδ hhalf hu hua ha hboundary
  calc
    MetricCodes.Johnson.variationalRate δ ≤
        MetricCodes.Johnson.shellRate A b g u :=
      MetricCodes.Johnson.variationalRate_le_of_feasible hfeasible
    _ < MetricCodes.Johnson.shellRate a 0 0 u := himprovement
    _ = MetricCodes.Johnson.mrrwRate δ := hrate.symm

theorem strict_mrrw2
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Johnson.combinedVariationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  rcases MetricCodes.Johnson.mrrw_endpoint_dichotomy hδ hhalf with
    hstrict | hendpoint
  · exact
      (MetricCodes.Johnson.combinedVariationalRate_le_shell δ).trans_lt
        (variationalRate_lt_mrrw_of_interior hδ hhalf hstrict)
  · exact MetricCodes.Johnson.combinedVariationalRate_lt_mrrw_of_endpoint
      hδ hhalf hendpoint

end

end MRRW

namespace Johnson

section

open scoped BigOperators InnerProductSpace Matrix

/-- The Boolean harmonic basis function indexed by a degree and basis coordinate in the shell
window. -/
def johnsonWindowBasis {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (Q : ShellWindowIndex n p q L) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.harmonicBasisFunction n
    (p + q + Q.1.val) (h.window_degree_half Q.1) Q.2

theorem johnsonWindowBasis_isHarmonic {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (Q : ShellWindowIndex n p q L) :
    MetricCodes.Boolean.IsHarmonic (p + q + Q.1.val)
      (johnsonWindowBasis h Q) := by
  exact MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n
    (p + q + Q.1.val) (h.window_degree_half Q.1) Q.2

/-- The orthonormal coordinates of a harmonic Boolean function in its global degree space. -/
def johnsonHarmonicCoordinates {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    Fin (MetricCodes.booleanHarmonicDimension n j) → ℝ :=
  fun a =>
    (MetricCodes.Boolean.harmonicOrthonormalBasis n j hj).repr
      (globalHarmonicVector f hf) a

/-- The adjacent Johnson channel matrix indexed by shell-window harmonic coordinates. -/
def johnsonWindowChannelMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ) :
    Matrix (Fin n × ShellWindowIndex n p q L)
      (ShellWindowIndex n p q L) ℝ :=
  fun T Q =>
    johnsonAdjacentBlockCoefficient n w p q L v lam T.2.1 Q.1 *
      johnsonHarmonicCoordinates (h.window_degree_half T.2.1)
        (johnsonAdjacentChannel n w p q L T.2.1 Q.1
          (johnsonWindowBasis h Q) T.1)
        (johnsonAdjacentChannel_isHarmonic h hstrict T.2.1 Q.1
          (johnsonWindowBasis h Q)
          (johnsonWindowBasis_isHarmonic h Q) T.1) T.2.2

/-- The shell-window channel matrix reindexed by the total Johnson ambient dimension. -/
def johnsonChannelMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ) :
    Matrix
      (Fin n × Fin (MetricCodes.johnsonAmbientDimension n (p + q) L))
      (Fin (MetricCodes.johnsonAmbientDimension n (p + q) L)) ℝ :=
  fun T Q =>
    johnsonWindowChannelMatrix h hstrict v lam
      (T.1, (shellWindowIndexEquiv n p q L h.first_le).symm T.2)
      ((shellWindowIndexEquiv n p q L h.first_le).symm Q)

/-- The enumeration flattening a coordinate and two ambient indices into one finite Gram index. -/
def johnsonGramIndexEquiv (n D : ℕ) :
    ((Fin n × Fin D) × Fin D) ≃ Fin (n * D * D) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin])

end

namespace SpectralAsymptotics

section

open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics

/-- The terminal degree shifted downward by a fixed window offset `r`. -/
def terminalIndex (u : ℝ) (r n : ℕ) : ℕ :=
  terminalDegree u n - r

/-- The dimensionless expression for the Johnson mu coefficient after scaling by the word
length. -/
def normalizedMu (j₁ j₂ j m e : ℝ) : ℝ :=
  (m / 2) *
    (j₂ * (j₂ + e) - j₁ * (j₁ + e)) /
      (j * (j + e))

/-- The limiting Johnson mu coefficient under proportional shell and degree scaling. -/
def muLimit (a b g u : ℝ) : ℝ :=
  (1 - 2 * a) *
      (1 - 2 * b - 2 * g) *
      MetricCodes.Johnson.centeredEta a b g /
    (4 * (1 - 2 * u) ^ 2)

/-- The dimensionless Johnson diagonal expression in terms of the normalized mu coefficient. -/
def normalizedDiagonal
    (j₁ j₂ j m e x y : ℝ) : ℝ :=
  (normalizedMu j₁ j₂ j m e - m ^ 2) / (x * y)

/-- The limiting Johnson diagonal coefficient under proportional shell and degree scaling. -/
def diagonalLimit (a b g u : ℝ) : ℝ :=
  (1 - 2 * a) *
      ((1 - 2 * b - 2 * g) *
        MetricCodes.Johnson.centeredEta a b g -
        (1 - 2 * a) *
          (1 - 2 * u) ^ 2) /
    ((1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2))

/-- The homogeneous square-root expression used to scale the Johnson nu coefficient. -/
def normalizedNu (j m eta sigma e : ℝ) : ℝ :=
  Real.sqrt
      ((j ^ 2 - m ^ 2) *
        (j ^ 2 - eta ^ 2) *
        ((sigma + e) ^ 2 - j ^ 2)) /
    (2 * j * Real.sqrt ((2 * j - e) * (2 * j + e)))

/-- The limiting normalized Johnson nu coefficient under proportional degree scaling. -/
def nuLimit (a b g u : ℝ) : ℝ :=
  Real.sqrt
      (((1 - 2 * u) ^ 2 -
          (1 - 2 * a) ^ 2) *
        ((1 - 2 * u) ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        ((1 - 2 * b - 2 * g) ^ 2 -
          (1 - 2 * u) ^ 2)) /
    (8 * (1 - 2 * u) ^ 2)

/-- The limiting Johnson edge coefficient under proportional shell and degree scaling. -/
def edgeLimit (a b g u : ℝ) : ℝ :=
  Real.sqrt
      (((1 - 2 * u) ^ 2 -
          (1 - 2 * a) ^ 2) *
        ((1 - 2 * u) ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        ((1 - 2 * b - 2 * g) ^ 2 -
          (1 - 2 * u) ^ 2)) /
    (2 * (1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2))

/-- The limiting hatted Johnson diagonal coefficient under proportional degree scaling. -/
def hattedDiagonalLimit (a b g u : ℝ) : ℝ :=
  ((1 - 2 * b - 2 * g) *
      MetricCodes.Johnson.centeredEta a b g -
      (1 - 2 * a) *
        (1 - 2 * u) ^ 2) ^ 2 /
    ((1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2) *
      (1 - (1 - 2 * u) ^ 2))

/-- The limiting hatted Johnson edge coefficient under proportional degree scaling. -/
def hattedEdgeLimit (a b g u : ℝ) : ℝ :=
  (((1 - 2 * u) ^ 2 -
      MetricCodes.Johnson.centeredEta a b g ^ 2) *
    ((1 - 2 * b - 2 * g) ^ 2 -
      (1 - 2 * u) ^ 2)) /
    (2 * (1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2) *
      Real.sqrt (1 - (1 - 2 * u) ^ 2))

/-- The terminal vector used in the Johnson-code argument. -/
def terminalVector (p q L m : ℕ) : MetricCodes.Johnson.Space p q L :=
  MetricCodes.Hamming.terminalVector (p + q) L m

/-- The Rayleigh quotient of the constant vector on a terminal window of `m + 1` Johnson
degrees. -/
def terminalRayleigh (a b g u : ℝ) (m n : ℕ) : ℝ :=
  ((∑ r ∈ Finset.range (m + 1),
      MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalIndex u (m - r) n)) +
    2 * ∑ r ∈ Finset.range m,
      MetricCodes.johnsonHattedEdge n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalIndex u (m - r) n)) /
    ((m : ℝ) + 1)

/-- The spectral gap used in the Johnson-code argument. -/
def spectralGap (d a b g u : ℝ) : ℝ :=
  (MetricCodes.Johnson.spectralLimit a b g u -
    MetricCodes.Johnson.asymptoticThreshold d a) / 4

end

end SpectralAsymptotics

section

open Filter Topology
open scoped Topology

namespace Rate

open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics

/-- The ratio of the threshold numerator to the positive spectral gap in the Johnson rate
certificate. -/
def certificateConstant (d a b g u : ℝ) : ℝ :=
  (2 - MetricCodes.Johnson.asymptoticThreshold d a) /
    spectralGap d a b g u

end Rate

end

section

open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics

end

end Johnson

section

open scoped BigOperators

namespace Numerics

/-- The fixed first parameter used in the certified numerical kissing-number estimate. -/
def kissingA : ℝ := 0.08570143806746

/-- The fixed second parameter used in the certified numerical kissing-number estimate. -/
def kissingB : ℝ := 0.00370282933568

/-- The log series lower used in the metric-code argument. -/
def logSeriesLower (x : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range m, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

/-- The log series upper used in the metric-code argument. -/
def logSeriesUpper (x : ℝ) (m : ℕ) : ℝ :=
  logSeriesLower x m + 2 * (x ^ (2 * m + 1) / (1 - x ^ 2))

end Numerics

end

namespace Spherical

section

theorem sphericalEntropy_continuous : Continuous MetricCodes.sphericalEntropy := by
  have hplus :
      Continuous (fun u : ℝ => (1 + u) * Real.log (1 + u)) := by
    simpa only [Function.comp_def, Pi.add_apply] using
      (Real.continuous_mul_log.comp (continuous_const.add continuous_id : Continuous (fun u : ℝ
        => 1 + u)))
  have hnatural : Continuous
      (fun u : ℝ =>
        ((1 + u) * Real.log (1 + u) - u * Real.log u) /
          Real.log 2) :=
    (hplus.sub Real.continuous_mul_log).div_const (Real.log 2)
  convert hnatural using 1
  funext u
  unfold MetricCodes.sphericalEntropy Real.logb
  ring

theorem hasDerivAt_sphericalEntropy {u : ℝ} (hu : 0 < u) :
    HasDerivAt MetricCodes.sphericalEntropy
      (Real.logb 2 ((1 + u) / u)) u := by
  have hplus :=
    (Real.hasDerivAt_mul_log (by linarith : 1 + u ≠ 0)).comp u
      ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u))
  have hself := Real.hasDerivAt_mul_log hu.ne'
  have hderiv := (hplus.sub hself).div_const (Real.log 2)
  have hfun : MetricCodes.sphericalEntropy =
      (fun x : ℝ =>
        ((1 + x) * Real.log (1 + x) - x * Real.log x) /
          Real.log 2) := by
    funext x
    unfold MetricCodes.sphericalEntropy Real.logb
    ring
  have hvalue :
      Real.logb 2 ((1 + u) / u) =
        (((Real.log (1 + u) + 1) * (0 + 1) -
          (Real.log u + 1)) / Real.log 2) := by
    unfold Real.logb
    rw [Real.log_div (by linarith : 1 + u ≠ 0) hu.ne']
    ring
  rw [hfun, hvalue]
  simpa only [Function.comp_apply, Pi.sub_apply] using hderiv

theorem sphericalEntropy_strictMono :
    StrictMonoOn MetricCodes.sphericalEntropy (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    sphericalEntropy_continuous.continuousOn
  intro u hu
  have hu' : 0 < u := by
    simpa only [interior_Ici, Set.mem_Ioi] using hu
  rw [(hasDerivAt_sphericalEntropy hu').deriv]
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  apply (lt_div_iff₀ hu').2
  linarith

theorem sphericalEntropy_sub_nonneg {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) :
    0 ≤ MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  have ha : 0 ≤ a := hb.trans hba
  exact sub_nonneg.mpr
    (sphericalEntropy_strictMono.monotoneOn hb ha hba)

/-- The feasible used in the spherical-code argument. -/
def Feasible (s a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ s < 2 * MetricCodes.Gamma a b

/-- The rate set used in the spherical-code argument. -/
def rateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible s a b ∧
    r = MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b}

/-- The variational rate used in the spherical-code argument. -/
def variationalRate (s : ℝ) : ℝ := sInf (rateSet s)

theorem rateSet_bddBelow (s : ℝ) : BddBelow (rateSet s) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, b, ⟨hb, hba, _⟩, rfl⟩
  exact sphericalEntropy_sub_nonneg hb.le hba.le

theorem variationalRate_le_of_feasible {s a b : ℝ}
    (h : Feasible s a b) :
    variationalRate s ≤
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  exact csInf_le (rateSet_bddBelow s) ⟨a, b, h, rfl⟩

end

section

open Filter Topology
open scoped Topology

theorem Gamma_zero {a : ℝ} (ha : 0 < a) :
    MetricCodes.Gamma a 0 =
      Real.sqrt (a * (1 + a)) / (1 + 2 * a) := by
  have hrad : 0 < a * (1 + a) := by positivity
  have hroot : Real.sqrt (a * (1 + a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hlin : 1 + 2 * a ≠ 0 := by positivity
  have hsquare := Real.sq_sqrt hrad.le
  rw [MetricCodes.Gamma_eq_sub]
  simp only [zero_mul, add_zero, sub_zero]
  field_simp [hroot, hlin]
  nlinarith

theorem classicalThreshold_spectral
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    2 * MetricCodes.Gamma (MetricCodes.classicalThreshold s) 0 = s := by
  have ha : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - s ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hrootsq := Real.sq_sqrt hrad.le
  have hidentity :
      4 * MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s) =
        s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 := by
    unfold MetricCodes.classicalThreshold
    field_simp [hroot.ne']
    nlinarith
  have hinner :
      0 < MetricCodes.classicalThreshold s *
        (1 + MetricCodes.classicalThreshold s) := by positivity
  have hinnersq := Real.sq_sqrt hinner.le
  have hlin : 0 < 1 + 2 * MetricCodes.classicalThreshold s := by positivity
  have htarget :
      2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s)) =
        s * (1 + 2 * MetricCodes.classicalThreshold s) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    calc
      (2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s))) ^ 2 =
          4 * MetricCodes.classicalThreshold s *
            (1 + MetricCodes.classicalThreshold s) := by
            rw [mul_pow, hinnersq]
            ring
      _ = s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 :=
        hidentity
      _ = (s * (1 + 2 * MetricCodes.classicalThreshold s)) ^ 2 := by
        ring
  rw [Gamma_zero ha, ← mul_div_assoc]
  exact (div_eq_iff hlin.ne').2 htarget

/-- The spherical improvement path used in the spherical-code argument. -/
def sphericalImprovementPath (a b : ℝ) : ℝ :=
  a + (4 * a + 3) * b

theorem sphericalImprovementSlope_gt_one {a : ℝ} (ha : 0 < a) :
    1 < (4 * a + 3) := by
  linarith

/-- The polynomial expression used to certify positivity of the spherical spectral margin. -/
def sphericalSpectralMarginPolynomial (a c b : ℝ) : ℝ :=
  let T := a * (1 + a)
  let l := 1 + 2 * a
  let p := c * l - 1
  let q := c ^ 2 - 1
  l ^ 2 *
      (T * (2 * p - c * l) +
        b * (p ^ 2 + 2 * T * q - T * c ^ 2) +
        2 * b ^ 2 * p * q + b ^ 3 * q ^ 2) -
    T * (4 * c * l + 4 * c ^ 2 * b) *
      (T + c * l * b + c ^ 2 * b ^ 2)

theorem sphericalSpectralMarginPolynomial_factor (a c b : ℝ) :
    (((a + c * b) * (1 + (a + c * b)) - b * (1 + b)) *
        (1 + 2 * a)) ^ 2 -
      a * (1 + a) * (1 + 2 * (a + c * b)) ^ 2 *
        ((a + c * b) * (1 + (a + c * b))) =
      b * sphericalSpectralMarginPolynomial a c b := by
  unfold sphericalSpectralMarginPolynomial
  ring

theorem sphericalSpectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (sphericalSpectralMarginPolynomial a c) := by
  unfold sphericalSpectralMarginPolynomial
  fun_prop

theorem sphericalSpectralMarginPolynomial_improvement_zero
    (a : ℝ) :
    sphericalSpectralMarginPolynomial a
      (4 * a + 3) 0 =
      a * (1 + a) * (1 + 2 * a) := by
  unfold sphericalSpectralMarginPolynomial
  ring

theorem eventually_Gamma_improvement {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.Gamma a 0 <
        MetricCodes.Gamma (sphericalImprovementPath a b) b := by
  have hzero :
      0 < sphericalSpectralMarginPolynomial a
        (4 * a + 3) 0 := by
    rw [sphericalSpectralMarginPolynomial_improvement_zero]
    positivity
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < sphericalSpectralMarginPolynomial a
          (4 * a + 3) b := by
    have hcontinuous :
        ContinuousAt
          (sphericalSpectralMarginPolynomial a
            (4 * a + 3)) 0 :=
      (sphericalSpectralMarginPolynomial_continuous
        a (4 * a + 3)).continuousAt
    exact nhdsWithin_le_nhds
      (hcontinuous.tendsto.eventually (lt_mem_nhds hzero))
  have hc : 1 < (4 * a + 3) :=
    sphericalImprovementSlope_gt_one ha
  filter_upwards [hpoly, self_mem_nhdsWithin]
    with b hbpoly (hb : 0 < b)
  have hbpath : b < sphericalImprovementPath a b := by
    unfold sphericalImprovementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < sphericalImprovementPath a b :=
    hb.trans hbpath
  have hbase : 0 < a * (1 + a) := by positivity
  have hrad :
      0 < sphericalImprovementPath a b *
        (1 + sphericalImprovementPath a b) := by positivity
  have hnum :
      0 < sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b) := by
    have hfactor :
        0 < (sphericalImprovementPath a b - b) *
          (1 + sphericalImprovementPath a b + b) := by positivity
    nlinarith
  have hmargin :
      0 <
        ((sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
          (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    have hfactor := sphericalSpectralMarginPolynomial_factor
      a (4 * a + 3) b
    change
      0 < (((a + (4 * a + 3) * b) *
          (1 + (a + (4 * a + 3) * b)) -
            b * (1 + b)) * (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * (a + (4 * a + 3) * b)) ^ 2 *
            ((a + (4 * a + 3) * b) *
              (1 + (a + (4 * a + 3) * b)))
    rw [hfactor]
    exact mul_pos hb hbpoly
  have hleftnonneg :
      0 ≤ Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) := by
    positivity
  have hrightpos :
      0 < (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
        (1 + 2 * a) := by positivity
  have hsquare :
      (Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)))) ^ 2 =
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hbase.le,
      Real.sq_sqrt hrad.le]
    ring
  have hcross :
      Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) <
        (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
            (1 + 2 * a) := by
    nlinarith
  rw [Gamma_zero ha, MetricCodes.Gamma_eq_sub]
  have hlin : 0 < 1 + 2 * a := by positivity
  have hden :
      0 < (1 + 2 * sphericalImprovementPath a b) *
        Real.sqrt
          (sphericalImprovementPath a b *
            (1 + sphericalImprovementPath a b)) := by positivity
  exact (div_lt_div_iff₀ hlin hden).2 hcross

theorem neg_mul_logb_le_sphericalEntropy {b : ℝ} (hb : 0 ≤ b) :
    b * (-Real.logb 2 b) ≤ MetricCodes.sphericalEntropy b := by
  have hlog : 0 ≤ Real.logb 2 (1 + b) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hterm : 0 ≤ (1 + b) * Real.logb 2 (1 + b) := by
    exact mul_nonneg (by linarith) hlog
  unfold MetricCodes.sphericalEntropy
  nlinarith

theorem eventually_sphericalEntropy_improvement {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy b < MetricCodes.sphericalEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.sphericalEntropy (sphericalImprovementPath a b)
  have hinner : DifferentiableAt ℝ (sphericalImprovementPath a) 0 := by
    unfold sphericalImprovementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (sphericalImprovementPath a 0) := by
    simpa only [sphericalImprovementPath, mul_zero, add_zero] using
      (hasDerivAt_sphericalEntropy ha).differentiableAt
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.sphericalEntropy
          (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, sphericalImprovementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  filter_upwards [hupper, hlog, self_mem_nhdsWithin]
    with b hbound hlogb (hb : 0 < b)
  have houter_bound :
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy a < b * M := by
    calc
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
          MetricCodes.sphericalEntropy a =
        b * (b⁻¹ *
          (MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a)) := by
          field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_sphericalEntropy hb.le
  linarith

theorem exists_strict_improving_spherical_feasible
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ a b : ℝ, Feasible s a b ∧
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  let a₀ : ℝ := MetricCodes.classicalThreshold s
  have ha₀ : 0 < a₀ := MetricCodes.classicalThreshold_pos hs hs'
  have hgamma := eventually_Gamma_improvement ha₀
  have hentropy := eventually_sphericalEntropy_improvement ha₀
  have hc : 1 < (4 * a₀ + 3) :=
    sphericalImprovementSlope_gt_one ha₀
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible s (sphericalImprovementPath a₀ b) b ∧
          MetricCodes.sphericalEntropy (sphericalImprovementPath a₀ b) -
            MetricCodes.sphericalEntropy b <
              MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
    filter_upwards [hgamma, hentropy, self_mem_nhdsWithin]
      with b hgamma' hentropy' (hb : 0 < b)
    have hbpath : b < sphericalImprovementPath a₀ b := by
      unfold sphericalImprovementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb, hbpath, ?_⟩
      have hboundary : 2 * MetricCodes.Gamma a₀ 0 = s := by
        dsimp [a₀]
        exact classicalThreshold_spectral hs hs'
      nlinarith
    · simpa only using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨sphericalImprovementPath a₀ b, b, hb⟩

end

end Spherical

end MetricCodes

namespace MetricCodes

namespace Spherical

section

open Filter Topology
open scoped Topology

end

section

open scoped BigOperators

namespace HigherHierarchy

/-- The spectral atom used in the spherical-code argument. -/
def spectralAtom (u : ℝ) : ℝ :=
  Real.sqrt (u * (1 + u)) / (1 + 2 * u)

/-- The interlacing used in the spherical-code argument. -/
def Interlacing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : Prop :=
  0 ≤ a (Fin.last r) ∧
    ∀ i : Fin r, a i.castSucc > b i ∧ b i > a i.succ

/-- The lagrange numerator used in the spherical-code argument. -/
def lagrangeNumerator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r, (((a ℓ) * (1 + (a ℓ))) - ((b m) * (1 + (b m))))

/-- The lagrange denominator used in the spherical-code argument. -/
def lagrangeDenominator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r,
    (((a ℓ) * (1 + (a ℓ))) - ((a (ℓ.succAbove m)) * (1 + (a (ℓ.succAbove m)))))

/-- The lagrange weight used in the spherical-code argument. -/
def lagrangeWeight {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  lagrangeNumerator a b ℓ / lagrangeDenominator a ℓ

/-- The gamma used in the spherical-code argument. -/
def Gamma {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ * spectralAtom (a ℓ)

/-- The phi used in the spherical-code argument. -/
def Phi {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (∑ ℓ : Fin (r + 1), MetricCodes.sphericalEntropy (a ℓ)) -
    ∑ m : Fin r, MetricCodes.sphericalEntropy (b m)

theorem Interlacing.strictAnti_ambient {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : StrictAnti a := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  exact (h.2 i).2.trans (h.2 i).1

theorem Interlacing.ambient_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin (r + 1)) : 0 ≤ a i := by
  exact h.1.trans (h.strictAnti_ambient.antitone i.le_last)

theorem Interlacing.stabilizer_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) : 0 < b i :=
  (h.ambient_nonneg i.succ).trans_lt (h.2 i).2

theorem quadraticCoordinate_strictMonoOn :
    StrictMonoOn (fun u : ℝ => u * (1 + u)) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  change x * (1 + x) < y * (1 + y)
  nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < 1 + x + y)]

/-- The monic polynomial with roots `b m * (1 + b m)` for the stabilizer parameters. -/
def stabilizerPolynomial {r : ℕ} (b : Fin r → ℝ) : Polynomial ℝ :=
  ∏ m : Fin r, (Polynomial.X - Polynomial.C (((b m) * (1 + (b m)))))

end HigherHierarchy

end

end Spherical

end MetricCodes

namespace MetricCodes

namespace Spherical

namespace HigherHierarchy

section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval

namespace Arcsine

end Arcsine

end

section

open MeasureTheory Real Set
open scoped Interval

namespace ArcsineIntegral

end ArcsineIntegral

end

section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology

namespace ArcsineTransform

end ArcsineTransform

end

end HigherHierarchy

section

open scoped BigOperators

namespace HigherHierarchyChebyshev

/-- The angle `j * π / N` used to parameterize the Chebyshev zeros. -/
def zeroAngle (N j : ℕ) : ℝ :=
  ((j : ℝ) * Real.pi) / (N : ℝ)

/-- The zero used in the spherical-code argument. -/
def zero (R : ℝ) (N j : ℕ) : ℝ :=
  R / 2 * (1 + Real.cos (zeroAngle N j))

/-- The stabilizer used in the spherical-code argument. -/
def stabilizer (R : ℝ) (r : ℕ) (i : Fin r) : ℝ :=
  (Real.sqrt (1 + 4 * (zero R (r + 1) (i.val + 1))) - 1) / 2

end HigherHierarchyChebyshev

end

end Spherical

end MetricCodes

namespace MetricCodes

namespace Spherical

namespace HigherHierarchy

section

open scoped BigOperators

namespace Numerics

/-- The kissing ambient used in the spherical-code argument. -/
def kissingAmbient : Fin 3 → ℝ :=
  ![(0.090531 : ℝ), 0.000565957168637484, 0.00000249433171106134]

/-- The kissing stabilizer used in the spherical-code argument. -/
def kissingStabilizer : Fin 2 → ℝ :=
  ![(0.00693131464159807 : ℝ), 0.0000438056170666568]

@[simp] theorem kissingAmbient_apply (i : Fin 3) :
    kissingAmbient i =
      if i.val = 0 then (0.090531 : ℝ)
      else if i.val = 1 then 0.000565957168637484
      else 0.00000249433171106134 := by
  fin_cases i <;> rfl

@[simp] theorem kissingStabilizer_apply (i : Fin 2) :
    kissingStabilizer i =
      if i.val = 0 then (0.00693131464159807 : ℝ)
      else 0.0000438056170666568 := by
  fin_cases i <;> rfl

@[simp] theorem succAbove_three_20 :
    (2 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
@[simp] theorem succAbove_three_21 :
    (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide

end Numerics

end

section

open Filter Topology
open scoped BigOperators Topology

/-- The hierarchy rate set used in the spherical-code argument. -/
def hierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ z = Phi a b}

/-- The hierarchy variational rate used in the spherical-code argument. -/
def hierarchyVariationalRate (s : ℝ) : ℝ := sInf (hierarchyRateSet s)

end

section

open MeasureTheory
open scoped BigOperators Interval

/-- The stieltjes phase used in the spherical-code argument. -/
def stieltjesPhase {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(a (Fin.last r)) * (1 + a (Fin.last r)), (t + u)⁻¹) +
    ∑ i : Fin r,
      ∫ u in ((b i) * (1 + (b i)))..(a i.castSucc) * (1 + a i.castSucc),
        (t + u)⁻¹

/-- The stieltjes phase product used in the spherical-code argument. -/
def stieltjesPhaseProduct {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  t * (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
    (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))

end

end HigherHierarchy

end Spherical

end MetricCodes

end MetricCodesNoncomputable
