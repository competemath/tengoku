import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12EulerSupport.endpointRatio_continuousOn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.endpointIntegrand_intervalIntegrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.endpointIntegrand_tendsto` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.endpointBound_integral` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.endpointIntegral_tendsto` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace Row12EulerSupport

noncomputable def endpointRatio (p y : ℝ) : ℝ :=
  (1 - y) / (1 - (1 - p) * y)

noncomputable def endpointIntegrand (p y : ℝ) : ℝ :=
  y ^ (-(5 : ℝ) / 6) * endpointRatio p y ^ ((5 : ℝ) / 6)

/--
@isnad1 id=lt.2h2v.s6.b9479a2d567e from=translated src=- shape=1005ffb2 vocab=85d98899
-/
theorem endpointDenominator_pos {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    0 < 1 - (1 - p) * y := by
  have hpy : 0 ≤ p * y := mul_nonneg hp.le hy.1
  rcases lt_or_eq_of_le hy.2 with hlt | rfl
  · nlinarith
  · simpa using hp

/--
@isnad1 id=le.2h2v.s5.e7e9be892083 from=translated src=- shape=341d216e vocab=d9b3bc71
-/
theorem endpointRatio_nonneg {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    0 ≤ endpointRatio p y :=
  div_nonneg (sub_nonneg.mpr hy.2) (endpointDenominator_pos hp hy).le

/--
@isnad1 id=le.2h2v.s5.16365beb71d0 from=translated src=- shape=3909491b vocab=d9b3bc71
-/
theorem endpointRatio_le_one {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    endpointRatio p y ≤ 1 := by
  unfold endpointRatio
  apply (div_le_one (endpointDenominator_pos hp hy)).2
  nlinarith [mul_nonneg hp.le hy.1]

/--
@isnad1 id=continuo.1h1v.s5.e0bb679cf7f0 from=translated src=- shape=4756762a vocab=16aafaf1
-/
theorem endpointRatio_continuousOn {p : ℝ} (hp : 0 < p) :
    ContinuousOn (endpointRatio p) (Icc 0 1) := by
  unfold endpointRatio
  refine (continuousOn_const.sub continuousOn_id).div
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
  intro y hy
  exact (endpointDenominator_pos hp hy).ne'

/--
@isnad1 id=le.2h2v.s5.648ed8282f80 from=translated src=- shape=341d216e vocab=95daed3a
-/
theorem endpointIntegrand_nonneg {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    0 ≤ endpointIntegrand p y := by
  exact mul_nonneg (Real.rpow_nonneg hy.1 _)
    (Real.rpow_nonneg (endpointRatio_nonneg hp hy) _)

/--
@isnad1 id=le.2h2v.s6.b33a58c52e03 from=translated src=- shape=c6c19f90 vocab=34f27084
-/
theorem endpointIntegrand_norm_le {p y : ℝ} (hp : 0 < p) (hy : y ∈ Icc 0 1) :
    ‖endpointIntegrand p y‖ ≤ y ^ (-(5 : ℝ) / 6) := by
  have hpow : endpointRatio p y ^ ((5 : ℝ) / 6) ≤ 1 := by
    simpa using Real.rpow_le_rpow (endpointRatio_nonneg hp hy)
      (endpointRatio_le_one hp hy) (by norm_num : (0 : ℝ) ≤ 5 / 6)
  rw [Real.norm_eq_abs, abs_of_nonneg (endpointIntegrand_nonneg hp hy)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hy.1 _) hpow

/--
@isnad1 id=interval.0h0v.s6.ce472d4610b5 from=translated src=- shape=e749861c vocab=557d60bc
-/
theorem endpointBound_intervalIntegrable :
    IntervalIntegrable (fun y : ℝ => y ^ (-(5 : ℝ) / 6)) volume 0 1 := by
  exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/--
@isnad1 id=aestrong.1h1v.s5.a217a72d18cd from=translated src=- shape=f273029f vocab=0685ab2c
-/
theorem endpointIntegrand_aestronglyMeasurable {p : ℝ} (hp : 0 < p) :
    AEStronglyMeasurable (endpointIntegrand p) (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hc : ContinuousOn (fun y => endpointRatio p y ^ ((5 : ℝ) / 6)) (Icc 0 1) :=
    (endpointRatio_continuousOn hp).rpow_const (fun _ _ => Or.inr (by norm_num))
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1)
  exact endpointBound_intervalIntegrable.aestronglyMeasurable_restrict_uIoc.mul
    ((hc.mono hsub).aestronglyMeasurable measurableSet_uIoc)

/--
@isnad1 id=interval.1h1v.s5.e01664f3595b from=translated src=- shape=e086963e vocab=16660712
-/
theorem endpointIntegrand_intervalIntegrable {p : ℝ} (hp : 0 < p) :
    IntervalIntegrable (endpointIntegrand p) volume 0 1 := by
  refine endpointBound_intervalIntegrable.mono_fun' (endpointIntegrand_aestronglyMeasurable hp) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  have hy' : y ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  exact endpointIntegrand_norm_le hp ⟨hy'.1.le, hy'.2⟩

/--
@isnad1 id=tendsto.1h1v.s5.ee8ca9fa719e from=translated src=- shape=80c91f73 vocab=e34605a2
-/
theorem endpointRatio_tendsto {y : ℝ} (hy : y < 1) :
    Tendsto (fun p : ℝ => endpointRatio p y) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hd : 1 - (1 - (0 : ℝ)) * y ≠ 0 := by nlinarith
  have hp : Tendsto (fun p : ℝ => p) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdlim : Tendsto (fun p : ℝ => 1 - (1 - p) * y) (𝓝[>] (0 : ℝ))
      (𝓝 (1 - (1 - (0 : ℝ)) * y)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.sub hp).mul_const y)
  have h : Tendsto (fun p : ℝ => (1 - y) / (1 - (1 - p) * y)) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 - y) / (1 - (1 - (0 : ℝ)) * y))) :=
    tendsto_const_nhds.div hdlim hd
  have hval : (1 - y) / (1 - (1 - (0 : ℝ)) * y) = 1 := by
    simp only [sub_zero, one_mul]
    exact div_self (by linarith : 1 - y ≠ 0)
  simpa only [endpointRatio, hval] using h

/--
@isnad1 id=tendsto.1h1v.s6.2e95c57bca7c from=translated src=- shape=d9c64292 vocab=e718cbf2
-/
theorem endpointIntegrand_tendsto {y : ℝ} (hy : y < 1) :
    Tendsto (fun p : ℝ => endpointIntegrand p y) (𝓝[>] (0 : ℝ))
      (𝓝 (y ^ (-(5 : ℝ) / 6))) := by
  have h : Tendsto (fun p : ℝ => y ^ (-(5 : ℝ) / 6) * endpointRatio p y ^ ((5 : ℝ) / 6))
      (𝓝[>] (0 : ℝ)) (𝓝 (y ^ (-(5 : ℝ) / 6) * (1 : ℝ) ^ ((5 : ℝ) / 6))) :=
    tendsto_const_nhds.mul
      ((endpointRatio_tendsto hy).rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))
  simpa only [endpointIntegrand, Real.one_rpow, mul_one] using h

/--
@isnad1 id=eq.0h0v.s6.a0dde0cd82de from=translated src=- shape=1a484a19 vocab=622f4513
-/
theorem endpointBound_integral :
    (∫ y in (0 : ℝ)..1, y ^ (-(5 : ℝ) / 6)) = 6 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(5 : ℝ) / 6))]
  norm_num [Real.zero_rpow]

/--
@isnad1 id=tendsto.0h0v.s6.d056e0a66418 from=translated src=- shape=63d00348 vocab=0f1c240f
-/
theorem endpointIntegral_tendsto :
    Tendsto (fun p : ℝ => ∫ y in (0 : ℝ)..1, endpointIntegrand p y)
      (𝓝[>] (0 : ℝ)) (𝓝 6) := by
  rw [← endpointBound_integral]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => y ^ (-(5 : ℝ) / 6))
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact endpointIntegrand_aestronglyMeasurable hp
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact Filter.Eventually.of_forall (fun y hy => by
      have hy' : y ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
      exact endpointIntegrand_norm_le hp ⟨hy'.1.le, hy'.2⟩)
  · exact endpointBound_intervalIntegrable
  · filter_upwards [volume.ae_ne (1 : ℝ)] with y hyne
    intro hy
    have hy' : y ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
    exact endpointIntegrand_tendsto (lt_of_le_of_ne hy'.2 hyne)

end Row12EulerSupport

