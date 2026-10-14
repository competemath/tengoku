/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.Feige.SteinIdentity

/-!
# Test functions for the exponential transfer identity

This file formalizes the two test functions used in the exponential transfer
identity.  They are written with `max` and `min`; for positive `c,d` this is
equivalent to the corresponding indicator notation and makes global
continuity transparent.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace Feige

namespace TransferTestFunctions

/-- `φ(x) = (1 - exp (-x/d)) 1_{x ≥ 0}` for `d > 0`. -/
noncomputable def transferPhi (d x : ℝ) : ℝ :=
  max 0 (1 - exp (-x / d))

/-- `ψ(x) = 1_{x ≥ 0} + exp (x/c) 1_{x < 0}` for `c > 0`. -/
noncomputable def transferPsi (c x : ℝ) : ℝ :=
  min 1 (exp (x / c))

/--
@isnad1 id=eq.2h2v.s5.111771ce82f6 from=translated src=- shape=10dc8d59 vocab=ed5c0424
-/
theorem transferPhi_of_nonneg {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) :
    transferPhi d x = 1 - exp (-x / d) := by
  rw [transferPhi, max_eq_right]
  exact sub_nonneg.mpr (exp_le_one_iff.mpr (by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hd.le))

/--
@isnad1 id=eq.2h2v.s5.3528b3b82824 from=translated src=- shape=1fd122ad vocab=0ee77ba7
-/
theorem transferPhi_of_nonpos {d x : ℝ} (hd : 0 < d) (hx : x ≤ 0) :
    transferPhi d x = 0 := by
  rw [transferPhi, max_eq_left]
  exact sub_nonpos.mpr (one_le_exp_iff.mpr (by
    exact div_nonneg (neg_nonneg.mpr hx) hd.le))

/--
@isnad1 id=eq.2h2v.s5.fb8f0364ee71 from=translated src=- shape=6bff1503 vocab=33838844
-/
theorem transferPsi_of_nonneg {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    transferPsi c x = 1 := by
  rw [transferPsi, min_eq_left]
  exact one_le_exp_iff.mpr (div_nonneg hx hc.le)

/--
@isnad1 id=eq.2h2v.s5.5e1e0fa2eaf1 from=translated src=- shape=0e347b3e vocab=c6bf9177
-/
theorem transferPsi_of_nonpos {c x : ℝ} (hc : 0 < c) (hx : x ≤ 0) :
    transferPsi c x = exp (x / c) := by
  rw [transferPsi, min_eq_right]
  exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hx hc.le)

/-- `φ` is continuous, including at its joining point zero.
@isnad1 id=continuo.0h1v.s4.d92b886e1507 from=translated src=- shape=f736e2c1 vocab=efb05c09
-/
theorem continuous_transferPhi (d : ℝ) : Continuous (transferPhi d) := by
  unfold transferPhi
  fun_prop

/-- `ψ` is continuous, including at its joining point zero.
@isnad1 id=continuo.0h1v.s4.39a607c3854e from=translated src=- shape=f736e2c1 vocab=25c3cb4a
-/
theorem continuous_transferPsi (c : ℝ) : Continuous (transferPsi c) := by
  unfold transferPsi
  fun_prop

/--
@isnad1 id=le.0h2v.s4.690513e13586 from=translated src=- shape=a120b2a8 vocab=462453ae
-/
theorem transferPhi_nonneg (d x : ℝ) : 0 ≤ transferPhi d x :=
  le_max_left _ _

/--
@isnad1 id=le.1h2v.s4.36fda69bc63a from=translated src=- shape=49f26697 vocab=0ee77ba7
-/
theorem transferPhi_le_one {d x : ℝ} (hd : 0 < d) :
    transferPhi d x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · rw [transferPhi_of_nonneg hd hx]
    linarith [exp_pos (-x / d)]
  · rw [transferPhi_of_nonpos hd (le_of_not_ge hx)]
    norm_num

/--
@isnad1 id=le.0h2v.s4.7f8110e451a8 from=translated src=- shape=a120b2a8 vocab=18180847
-/
theorem transferPsi_nonneg (c x : ℝ) : 0 ≤ transferPsi c x := by
  exact le_min zero_le_one (exp_pos _).le

/--
@isnad1 id=le.0h2v.s4.339954348222 from=translated src=- shape=aa052b1b vocab=18180847
-/
theorem transferPsi_le_one (c x : ℝ) : transferPsi c x ≤ 1 :=
  min_le_left _ _

/--
@isnad1 id=le.1h2v.s4.824dea764261 from=translated src=- shape=ef86dd10 vocab=00ffcbae
-/
theorem norm_transferPhi_le_one {d : ℝ} (hd : 0 < d) (x : ℝ) :
    ‖transferPhi d x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (transferPhi_nonneg d x)]
  exact transferPhi_le_one hd

/--
@isnad1 id=le.0h2v.s4.c351812bddf8 from=translated src=- shape=4ed13b70 vocab=26f76d30
-/
theorem norm_transferPsi_le_one (c x : ℝ) :
    ‖transferPsi c x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (transferPsi_nonneg c x)]
  exact transferPsi_le_one c x

/-- Exponential-weight integrability required by the Stein identity.
@isnad1 id=integrab.1h3v.s6.bcff94dd45eb from=translated src=- shape=30565abf vocab=da34a7f6
-/
theorem integrableOn_transferPhi_affine_mul_exp
    {d : ℝ} (hd : 0 < d) (y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => transferPhi d (y + a * e) * exp (-e)) (Ioi 0) :=
  Feige.ExponentialStein.integrableOn_comp_mul_exp
    (continuous_transferPhi d) (norm_transferPhi_le_one hd) y a

/--
@isnad1 id=integrab.0h3v.s6.753fed827777 from=translated src=- shape=d6a743c5 vocab=5fb96a78
-/
theorem integrableOn_transferPsi_affine_mul_exp
    (c y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => transferPsi c (y + a * e) * exp (-e)) (Ioi 0) :=
  Feige.ExponentialStein.integrableOn_comp_mul_exp
    (continuous_transferPsi c) (norm_transferPsi_le_one c) y a

/-- Exponential damping supplies the boundary term at infinity.
@isnad1 id=tendsto.1h3v.s6.3bae3367ffcf from=translated src=- shape=14179f27 vocab=cc3a1f7f
-/
theorem tendsto_transferPhi_affine_mul_exp_atTop
    {d : ℝ} (hd : 0 < d) (y a : ℝ) :
    Tendsto (fun e : ℝ => transferPhi d (y + a * e) * exp (-e))
      atTop (𝓝 0) :=
  Feige.ExponentialStein.tendsto_comp_mul_exp_atTop
    (norm_transferPhi_le_one hd) y a

/--
@isnad1 id=tendsto.0h3v.s5.102675316b89 from=translated src=- shape=1cb1f588 vocab=5a02ac18
-/
theorem tendsto_transferPsi_affine_mul_exp_atTop
    (c y a : ℝ) :
    Tendsto (fun e : ℝ => transferPsi c (y + a * e) * exp (-e))
      atTop (𝓝 0) :=
  Feige.ExponentialStein.tendsto_comp_mul_exp_atTop
    (norm_transferPsi_le_one c) y a

/-- Derivative of `φ` on the positive half-line.
@isnad1 id=hasderiv.2h2v.s6.742f44d9bb6e from=translated src=- shape=d941145d vocab=c00c5d7d
-/
theorem hasDerivAt_transferPhi_of_pos
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    HasDerivAt (transferPhi d) (exp (-x / d) / d) x := by
  have hloc : ∀ᶠ z in 𝓝 x, 0 ≤ z := eventually_ge_nhds hx
  apply HasDerivAt.congr_of_eventuallyEq
    (show HasDerivAt (fun z : ℝ => 1 - exp (-z / d))
        (exp (-x / d) / d) x by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
        ((((hasDerivAt_id x).div_const d).neg).exp.const_sub (1 : ℝ)))
  filter_upwards [hloc] with z hz
  exact transferPhi_of_nonneg hd hz

/-- Derivative of `φ` on the negative half-line.
@isnad1 id=hasderiv.2h2v.s5.524083a04252 from=translated src=- shape=9f5e0529 vocab=99124fde
-/
theorem hasDerivAt_transferPhi_of_neg
    {d x : ℝ} (hd : 0 < d) (hx : x < 0) :
    HasDerivAt (transferPhi d) 0 x := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const x 0)
  filter_upwards [eventually_le_nhds hx] with z hz
  exact transferPhi_of_nonpos hd hz

/-- Derivative of `ψ` on the positive half-line.
@isnad1 id=hasderiv.2h2v.s5.d092378d13f4 from=translated src=- shape=0cfdcdd6 vocab=d3e14d48
-/
theorem hasDerivAt_transferPsi_of_pos
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (transferPsi c) 0 x := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const x 1)
  filter_upwards [eventually_ge_nhds hx] with z hz
  exact transferPsi_of_nonneg hc hz

/-- Derivative of `ψ` on the negative half-line.
@isnad1 id=hasderiv.2h2v.s6.f04ed95d4f27 from=translated src=- shape=0b3366ca vocab=423a3874
-/
theorem hasDerivAt_transferPsi_of_neg
    {c x : ℝ} (hc : 0 < c) (hx : x < 0) :
    HasDerivAt (transferPsi c) (exp (x / c) / c) x := by
  have hloc : ∀ᶠ z in 𝓝 x, z ≤ 0 := eventually_le_nhds hx
  apply HasDerivAt.congr_of_eventuallyEq
    (show HasDerivAt (fun z : ℝ => exp (z / c))
        (exp (x / c) / c) x by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
        (((hasDerivAt_id x).div_const c).exp))
  filter_upwards [hloc] with z hz
  exact transferPsi_of_nonpos hc hz

/-- Away from zero, `φ'` has the piecewise formula used by the transfer
identity.
@isnad1 id=hasderiv.2h2v.s6.c3ced225bb2b from=translated src=- shape=6f4f8415 vocab=f5c95f61
-/
theorem hasDerivAt_transferPhi_of_ne_zero
    {d x : ℝ} (hd : 0 < d) (hx : x ≠ 0) :
    HasDerivAt (transferPhi d)
      (if 0 < x then exp (-x / d) / d else 0) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [ite_eq_right (not_lt_of_ge hxneg.le)]
    exact hasDerivAt_transferPhi_of_neg hd hxneg
  · rw [ite_eq_left hxpos]
    exact hasDerivAt_transferPhi_of_pos hd hxpos

/-- Away from zero, `ψ'` has the piecewise formula used by the transfer
identity.
@isnad1 id=hasderiv.2h2v.s6.c4d0a6923dee from=translated src=- shape=0f34836c vocab=0507febb
-/
theorem hasDerivAt_transferPsi_of_ne_zero
    {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    HasDerivAt (transferPsi c)
      (if x < 0 then exp (x / c) / c else 0) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [ite_eq_left hxneg]
    exact hasDerivAt_transferPsi_of_neg hc hxneg
  · rw [ite_eq_right (not_lt_of_ge hxpos.le)]
    exact hasDerivAt_transferPsi_of_pos hc hxpos

/-- The a.e. derivative used when applying Stein's identity to `φ`. -/
noncomputable def transferPhiDeriv (d x : ℝ) : ℝ :=
  if 0 < x then exp (-x / d) / d else 0

/-- The a.e. derivative used when applying Stein's identity to `ψ`. -/
noncomputable def transferPsiDeriv (c x : ℝ) : ℝ :=
  if x < 0 then exp (x / c) / c else 0

/--
@isnad1 id=measurab.0h1v.s3.2da9b1852f45 from=translated src=- shape=f736e2c1 vocab=fcd5aa63
-/
theorem measurable_transferPhiDeriv (d : ℝ) :
    Measurable (transferPhiDeriv d) := by
  unfold transferPhiDeriv
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const

/--
@isnad1 id=measurab.0h1v.s3.111c60894835 from=translated src=- shape=f736e2c1 vocab=6076e5bd
-/
theorem measurable_transferPsiDeriv (c : ℝ) :
    Measurable (transferPsiDeriv c) := by
  unfold transferPsiDeriv
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (by fun_prop) measurable_const

/--
@isnad1 id=le.1h2v.s5.720535832770 from=translated src=- shape=795ca0c1 vocab=292f7a4a
-/
theorem norm_transferPhiDeriv_le {d : ℝ} (hd : 0 < d) (x : ℝ) :
    ‖transferPhiDeriv d x‖ ≤ 1 / d := by
  unfold transferPhiDeriv
  split_ifs with hx
  · rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) hd)]
    exact div_le_div_of_nonneg_right
      (exp_le_one_iff.mpr (by
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) hd.le))
      hd.le
  · simp [hd.le]

/--
@isnad1 id=le.1h2v.s5.09881b5245d7 from=translated src=- shape=795ca0c1 vocab=739595c8
-/
theorem norm_transferPsiDeriv_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ‖transferPsiDeriv c x‖ ≤ 1 / c := by
  unfold transferPsiDeriv
  split_ifs with hx
  · rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) hc)]
    exact div_le_div_of_nonneg_right
      (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hx.le hc.le))
      hc.le
  · simp [hc.le]

/-- Weighted integrability of the formal derivative of `φ` along an
affine path.
@isnad1 id=integrab.1h3v.s6.f18864f5b501 from=translated src=- shape=355ec760 vocab=75b6e3ee
-/
theorem integrableOn_transferPhiDeriv_affine_mul_exp
    {d : ℝ} (hd : 0 < d) (y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => a * transferPhiDeriv d (y + a * e) * exp (-e))
      (Ioi 0) := by
  have hdom := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (|a| / d)
  apply hdom.mono'
  · exact (((measurable_const.mul
      ((measurable_transferPhiDeriv d).comp
        (measurable_const.add (measurable_const.mul measurable_id)))).mul
          (measurable_exp.comp measurable_id.neg)).aestronglyMeasurable)
  · filter_upwards with e
    rw [norm_mul, norm_mul, Real.norm_eq_abs, norm_of_nonneg (exp_pos _).le]
    calc
      |a| * ‖transferPhiDeriv d (y + a * e)‖ * exp (-e) ≤
          |a| * (1 / d) * exp (-e) := by
            gcongr
            exact norm_transferPhiDeriv_le hd _
      _ = |a| / d * exp (-1 * e) := by simp [div_eq_mul_inv]

/-- Weighted integrability of the formal derivative of `ψ`.
@isnad1 id=integrab.1h3v.s6.68cad48814fe from=translated src=- shape=355ec760 vocab=93e86c6f
-/
theorem integrableOn_transferPsiDeriv_affine_mul_exp
    {c : ℝ} (hc : 0 < c) (y a : ℝ) :
    IntegrableOn
      (fun e : ℝ => a * transferPsiDeriv c (y + a * e) * exp (-e))
      (Ioi 0) := by
  have hdom := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (|a| / c)
  apply hdom.mono'
  · exact (((measurable_const.mul
      ((measurable_transferPsiDeriv c).comp
        (measurable_const.add (measurable_const.mul measurable_id)))).mul
          (measurable_exp.comp measurable_id.neg)).aestronglyMeasurable)
  · filter_upwards with e
    rw [norm_mul, norm_mul, Real.norm_eq_abs, norm_of_nonneg (exp_pos _).le]
    calc
      |a| * ‖transferPsiDeriv c (y + a * e)‖ * exp (-e) ≤
          |a| * (1 / c) * exp (-e) := by
            gcongr
            exact norm_transferPsiDeriv_le hc _
      _ = |a| / c * exp (-1 * e) := by simp [div_eq_mul_inv]

/-- The formal derivative of `φ` is integrable on every finite
interval.
@isnad1 id=interval.2h5v.s6.e516a5790a23 from=translated src=- shape=8adc1439 vocab=6e823828
-/
theorem intervalIntegrable_transferPhiDeriv_affine
    {d : ℝ} (hd : 0 < d) (y a r s : ℝ) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun e : ℝ => a * transferPhiDeriv d (y + a * e))
      volume r s := by
  rw [intervalIntegrable_iff]
  rw [uIoc_of_le hrs]
  apply volume.integrableOn_of_bounded measure_Ioc_lt_top.ne
    ((measurable_const.mul
      ((measurable_transferPhiDeriv d).comp
        (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable)
  all_goals
    filter_upwards with e
    calc
      ‖a * transferPhiDeriv d (y + a * e)‖ =
          |a| * ‖transferPhiDeriv d (y + a * e)‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |a| * (1 / d) :=
        mul_le_mul_of_nonneg_left (norm_transferPhiDeriv_le hd _) (abs_nonneg a)

/-- The formal derivative of `ψ` is integrable on every finite
interval.
@isnad1 id=interval.2h5v.s6.57923a8b1e11 from=translated src=- shape=8adc1439 vocab=3894e5ef
-/
theorem intervalIntegrable_transferPsiDeriv_affine
    {c : ℝ} (hc : 0 < c) (y a r s : ℝ) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun e : ℝ => a * transferPsiDeriv c (y + a * e))
      volume r s := by
  rw [intervalIntegrable_iff]
  rw [uIoc_of_le hrs]
  apply volume.integrableOn_of_bounded measure_Ioc_lt_top.ne
    ((measurable_const.mul
      ((measurable_transferPsiDeriv c).comp
        (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable)
  all_goals
    filter_upwards with e
    calc
      ‖a * transferPsiDeriv c (y + a * e)‖ =
          |a| * ‖transferPsiDeriv c (y + a * e)‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |a| * (1 / c) :=
        mul_le_mul_of_nonneg_left (norm_transferPsiDeriv_le hc _) (abs_nonneg a)

/-- An affine path hits the exceptional point zero only on a null set,
so the composite `φ (y + a e)` has the expected derivative a.e.
@isnad1 id=eventual.2h3v.s7.236c2267f9df from=translated src=- shape=bf7d0c94 vocab=b9c492ab
-/
theorem ae_hasDerivAt_transferPhi_comp_affine
    {d y a : ℝ} (hd : 0 < d) (ha : a ≠ 0) :
    ∀ᵐ e : ℝ,
      HasDerivAt (transferPhi d ∘ fun t : ℝ => y + a * t)
        (a * transferPhiDeriv d (y + a * e)) e := by
  have hnull : volume {e : ℝ | y + a * e = 0} = 0 := by
    have hset : {e : ℝ | y + a * e = 0} = {-y / a} := by
      ext e
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor <;> intro h
      · apply (eq_div_iff ha).2
        linarith
      · rw [h]
        field_simp
        ring
    rw [hset]
    simp
  have hae : ∀ᵐ e : ℝ, y + a * e ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with e he
  have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
    simpa using
      ((hasDerivAt_const_mul a :
        HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
  simpa [transferPhiDeriv, mul_comm] using
    (hasDerivAt_transferPhi_of_ne_zero hd he).comp e haff

/-- The analogous a.e. composite derivative statement for `ψ`.
@isnad1 id=eventual.2h3v.s7.94dab34f0904 from=translated src=- shape=bf7d0c94 vocab=cfdc94ca
-/
theorem ae_hasDerivAt_transferPsi_comp_affine
    {c y a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    ∀ᵐ e : ℝ,
      HasDerivAt (transferPsi c ∘ fun t : ℝ => y + a * t)
        (a * transferPsiDeriv c (y + a * e)) e := by
  have hnull : volume {e : ℝ | y + a * e = 0} = 0 := by
    have hset : {e : ℝ | y + a * e = 0} = {-y / a} := by
      ext e
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor <;> intro h
      · apply (eq_div_iff ha).2
        linarith
      · rw [h]
        field_simp
        ring
    rw [hset]
    simp
  have hae : ∀ᵐ e : ℝ, y + a * e ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with e he
  have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
    simpa using
      ((hasDerivAt_const_mul a :
        HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
  simpa [transferPsiDeriv, mul_comm] using
    (hasDerivAt_transferPsi_of_ne_zero hc he).comp e haff

/-- Fixed-`y`, positive-scale one-sided Stein identity for the first test
function.  The proof splits according to whether the unique affine kink
`-y/a` lies in the positive half-line.
@isnad1 id=eq.2h3v.s7.7034b5bc2e3e from=translated src=- shape=8d506596 vocab=7f4f6d2b
-/
theorem transferPhi_stein_fixed
    {d y a : ℝ} (hd : 0 < d) (ha : a ≠ 0) :
    (∫ e : ℝ in Ioi 0, transferPhi d (y + a * e) * exp (-e)) -
        transferPhi d y =
      ∫ e : ℝ in Ioi 0,
        a * transferPhiDeriv d (y + a * e) * exp (-e) := by
  let u : ℝ → ℝ := transferPhi d ∘ fun e => y + a * e
  let du : ℝ → ℝ := fun e => a * transferPhiDeriv d (y + a * e)
  let v : ℝ → ℝ := fun e => exp (-e)
  let dv : ℝ → ℝ := fun e => -exp (-e)
  have hucont : Continuous u := by
    exact (continuous_transferPhi d).comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hvcont : Continuous v := by
    exact continuous_exp.comp continuous_id.neg
  have hvderiv : ∀ e, 0 < e → HasDerivAt v (dv e) e := by
    intro e _
    simpa [v, dv] using ((hasDerivAt_id e).neg.exp)
  have hu_deriv : ∀ e, 0 < e → y + a * e ≠ 0 →
      HasDerivAt u (du e) e := by
    intro e _ he
    have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
      simpa using
        ((hasDerivAt_const_mul a :
          HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
    simpa [u, du, transferPhiDeriv, mul_comm] using
      (hasDerivAt_transferPhi_of_ne_zero hd he).comp e haff
  have hu_int := integrableOn_transferPhi_affine_mul_exp hd y a
  have hdu_int := integrableOn_transferPhiDeriv_affine_mul_exp hd y a
  have huvNeg_int : IntegrableOn (u * dv) (Ioi (0 : ℝ)) := by
    rw [show u * dv =
      fun e => -(transferPhi d (y + a * e) * exp (-e)) by
        funext e
        simp [u, dv]]
    exact hu_int.neg
  have hduv_int : IntegrableOn (du * v) (Ioi (0 : ℝ)) := by
    rw [show du * v =
      fun e => a * transferPhiDeriv d (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact hdu_int
  have htop : Tendsto (u * v) atTop (𝓝 (0 : ℝ)) := by
    rw [show u * v =
      fun e => transferPhi d (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact tendsto_transferPhi_affine_mul_exp_atTop hd y a
  by_cases hk : 0 < -y / a
  · have huk : ∀ e, 0 < e → e ≠ -y / a → HasDerivAt u (du e) e := by
      intro e he hne
      apply hu_deriv e he
      intro hzero
      apply hne
      apply (eq_div_iff ha).2
      linarith
    have huFin : IntervalIntegrable du volume 0 (-y / a) := by
      exact intervalIntegrable_transferPhiDeriv_affine hd y a 0 (-y / a) hk.le
    have hvFin : IntervalIntegrable dv volume 0 (-y / a) := by
      have hdv : Continuous dv := by
        simp only [dv]
        fun_prop
      exact hdv.intervalIntegrable 0 (-y / a)
    have hip := Feige.ExponentialStein.integral_Ioi_mul_deriv_one_kink
      (u := u) (v := v) (u' := du) (v' := dv)
      (k := -y / a) (a' := transferPhi d y) (b' := 0)
      hk hucont hvcont huk hvderiv huFin hvFin
      huvNeg_int hduv_int (by simp [u, v]) htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip
  · have huall : ∀ e ∈ Ioi (0 : ℝ), HasDerivAt u (du e) e := by
      intro e he
      apply hu_deriv e he
      intro hzero
      apply hk
      rw [show -y / a = e by
        apply (div_eq_iff ha).2
        linarith]
      exact he
    have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ))
        (𝓝 (transferPhi d y)) := by
      have hc : Tendsto (u * v) (𝓝 (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        (hucont.mul hvcont).continuousAt
      have hc' : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        hc.mono_left inf_le_left
      rw [show (u * v) 0 = transferPhi d y by simp [u, v]] at hc'
      exact hc'
    have hip := integral_Ioi_mul_deriv_eq_deriv_mul
      (a := 0) (a' := transferPhi d y) (b' := 0)
      huall hvderiv huvNeg_int hduv_int hzero htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip

/-- Fixed-`y`, positive-scale one-sided Stein identity for `ψ`.
@isnad1 id=eq.2h3v.s7.a8d94cfe2248 from=translated src=- shape=8d506596 vocab=b6429784
-/
theorem transferPsi_stein_fixed
    {c y a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    (∫ e : ℝ in Ioi 0, transferPsi c (y + a * e) * exp (-e)) -
        transferPsi c y =
      ∫ e : ℝ in Ioi 0,
        a * transferPsiDeriv c (y + a * e) * exp (-e) := by
  let u : ℝ → ℝ := transferPsi c ∘ fun e => y + a * e
  let du : ℝ → ℝ := fun e => a * transferPsiDeriv c (y + a * e)
  let v : ℝ → ℝ := fun e => exp (-e)
  let dv : ℝ → ℝ := fun e => -exp (-e)
  have hucont : Continuous u := by
    exact (continuous_transferPsi c).comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hvcont : Continuous v := by
    exact continuous_exp.comp continuous_id.neg
  have hvderiv : ∀ e, 0 < e → HasDerivAt v (dv e) e := by
    intro e _
    simpa [v, dv] using ((hasDerivAt_id e).neg.exp)
  have hu_deriv : ∀ e, 0 < e → y + a * e ≠ 0 →
      HasDerivAt u (du e) e := by
    intro e _ he
    have haff : HasDerivAt (fun t : ℝ => y + a * t) a e := by
      simpa using
        ((hasDerivAt_const_mul a :
          HasDerivAt (fun t : ℝ => a * t) a e).const_add y)
    simpa [u, du, transferPsiDeriv, mul_comm] using
      (hasDerivAt_transferPsi_of_ne_zero hc he).comp e haff
  have hu_int := integrableOn_transferPsi_affine_mul_exp c y a
  have hdu_int := integrableOn_transferPsiDeriv_affine_mul_exp hc y a
  have huvNeg_int : IntegrableOn (u * dv) (Ioi (0 : ℝ)) := by
    rw [show u * dv =
      fun e => -(transferPsi c (y + a * e) * exp (-e)) by
        funext e
        simp [u, dv]]
    exact hu_int.neg
  have hduv_int : IntegrableOn (du * v) (Ioi (0 : ℝ)) := by
    rw [show du * v =
      fun e => a * transferPsiDeriv c (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact hdu_int
  have htop : Tendsto (u * v) atTop (𝓝 (0 : ℝ)) := by
    rw [show u * v =
      fun e => transferPsi c (y + a * e) * exp (-e) by
        funext e
        rfl]
    exact tendsto_transferPsi_affine_mul_exp_atTop c y a
  by_cases hk : 0 < -y / a
  · have huk : ∀ e, 0 < e → e ≠ -y / a → HasDerivAt u (du e) e := by
      intro e he hne
      apply hu_deriv e he
      intro hzero
      apply hne
      apply (eq_div_iff ha).2
      linarith
    have huFin : IntervalIntegrable du volume 0 (-y / a) :=
      intervalIntegrable_transferPsiDeriv_affine hc y a 0 (-y / a) hk.le
    have hvFin : IntervalIntegrable dv volume 0 (-y / a) := by
      have hdv : Continuous dv := by
        simp only [dv]
        fun_prop
      exact hdv.intervalIntegrable 0 (-y / a)
    have hip := Feige.ExponentialStein.integral_Ioi_mul_deriv_one_kink
      (u := u) (v := v) (u' := du) (v' := dv)
      (k := -y / a) (a' := transferPsi c y) (b' := 0)
      hk hucont hvcont huk hvderiv huFin hvFin
      huvNeg_int hduv_int (by simp [u, v]) htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip
  · have huall : ∀ e ∈ Ioi (0 : ℝ), HasDerivAt u (du e) e := by
      intro e he
      apply hu_deriv e he
      intro hzero
      apply hk
      rw [show -y / a = e by
        apply (div_eq_iff ha).2
        linarith]
      exact he
    have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ))
        (𝓝 (transferPsi c y)) := by
      have hz : Tendsto (u * v) (𝓝 (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        (hucont.mul hvcont).continuousAt
      have hz' : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 ((u * v) 0)) :=
        hz.mono_left inf_le_left
      rw [show (u * v) 0 = transferPsi c y by simp [u, v]] at hz'
      exact hz'
    have hip := integral_Ioi_mul_deriv_eq_deriv_mul
      (a := 0) (a' := transferPsi c y) (b' := 0)
      huall hvderiv huvNeg_int hduv_int hzero htop
    dsimp [u, du, v, dv] at hip
    simp_rw [mul_neg] at hip
    rw [integral_neg] at hip
    linear_combination -hip

/-- Negative-affine fixed-`y` Stein identity for `φ`.
@isnad1 id=eq.2h3v.s7.f3b08c380398 from=translated src=- shape=3ae852eb vocab=f7c439f1
-/
theorem transferPhi_stein_fixed_sub
    {d y b : ℝ} (hd : 0 < d) (hb : 0 < b) :
    transferPhi d y -
        (∫ e : ℝ in Ioi 0, transferPhi d (y - b * e) * exp (-e)) =
      ∫ e : ℝ in Ioi 0,
        b * transferPhiDeriv d (y - b * e) * exp (-e) := by
  have h := transferPhi_stein_fixed (y := y) (a := -b) hd (neg_ne_zero.mpr hb.ne')
  have hn := congrArg Neg.neg h
  simpa [sub_eq_add_neg, neg_mul, ← integral_neg, mul_assoc] using hn

/-- Negative-affine fixed-`y` Stein identity for `ψ`.
@isnad1 id=eq.2h3v.s7.56f90db9356b from=translated src=- shape=3ae852eb vocab=3104d1ae
-/
theorem transferPsi_stein_fixed_sub
    {c y b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    transferPsi c y -
        (∫ e : ℝ in Ioi 0, transferPsi c (y - b * e) * exp (-e)) =
      ∫ e : ℝ in Ioi 0,
        b * transferPsiDeriv c (y - b * e) * exp (-e) := by
  have h := transferPsi_stein_fixed (y := y) (a := -b) hc (neg_ne_zero.mpr hb.ne')
  have hn := congrArg Neg.neg h
  simpa [sub_eq_add_neg, neg_mul, ← integral_neg, mul_assoc] using hn

/-- Fixed-`y` two-sided exponential Stein identity for `φ`.
@isnad1 id=eq.3h4v.s8.1cc8d8c6fb88 from=translated src=- shape=dfdc2868 vocab=7f4f6d2b
-/
theorem transferPhi_stein_fixed_two_sided
    {d y a b : ℝ} (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    (∫ e : ℝ in Ioi 0, transferPhi d (y + a * e) * exp (-e)) -
        (∫ e : ℝ in Ioi 0, transferPhi d (y - b * e) * exp (-e)) =
      (∫ e : ℝ in Ioi 0,
        a * transferPhiDeriv d (y + a * e) * exp (-e)) +
      (∫ e : ℝ in Ioi 0,
        b * transferPhiDeriv d (y - b * e) * exp (-e)) := by
  have hp := transferPhi_stein_fixed (y := y) (a := a) hd ha.ne'
  have hm := transferPhi_stein_fixed_sub (y := y) hd hb
  linear_combination hp + hm

/-- Fixed-`y` two-sided exponential Stein identity for `ψ`.
@isnad1 id=eq.3h4v.s8.490869231d73 from=translated src=- shape=dfdc2868 vocab=b6429784
-/
theorem transferPsi_stein_fixed_two_sided
    {c y a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    (∫ e : ℝ in Ioi 0, transferPsi c (y + a * e) * exp (-e)) -
        (∫ e : ℝ in Ioi 0, transferPsi c (y - b * e) * exp (-e)) =
      (∫ e : ℝ in Ioi 0,
        a * transferPsiDeriv c (y + a * e) * exp (-e)) +
      (∫ e : ℝ in Ioi 0,
        b * transferPsiDeriv c (y - b * e) * exp (-e)) := by
  have hp := transferPsi_stein_fixed (y := y) (a := a) hc ha.ne'
  have hm := transferPsi_stein_fixed_sub (y := y) hc hb
  linear_combination hp + hm

end TransferTestFunctions

end Feige
