import Tengoku.Pi2Lean.Row12.BetaMoments
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Continuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12EulerSupport.eulerFunctionIntegrand_integrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.eulerFunctionIntegral_nonneg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.eulerFunctionIntegral_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.eulerFunctionIntegral_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.functionIntegralEndpoint_tendsto` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set intervalIntegral Filter Topology

namespace Row12EulerSupport

private theorem functionIntegralBase_lower {p x : ℝ} (hp1 : p < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) : p ≤ 1 - (1 - p) * x := by
  have hm := mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ 1 - p by linarith)
  nlinarith

/--
@isnad1 id=interval.2h1v.s7.0e97fed9b1c1 from=translated src=- shape=6984fb86 vocab=b0fe41ae
-/
theorem eulerFunctionIntegrand_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IntervalIntegrable
      (fun x : ℝ => Row12.betaDensity (5 / 6) x *
        (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) volume 0 1 := by
  have hd : IntervalIntegrable (fun x : ℝ => Row12.betaDensity (5 / 6) x) volume 0 1 := by
    simpa only [pow_zero, one_mul] using
      Row12.betaDensity_moment_integrable (a := (5 / 6 : ℝ)) (by norm_num) (by norm_num) 0
  apply hd.mul_continuousOn
  apply (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).rpow_const
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  exact Or.inl (ne_of_gt (lt_of_lt_of_le hp (functionIntegralBase_lower hp1 hx)))

/--
@isnad1 id=le.2h1v.s7.40e426881327 from=translated src=- shape=1c22aa1e vocab=eb5c703f
-/
theorem eulerFunctionIntegral_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ ∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
      (1 - (1 - p) * x) ^ (-1 / 6 : ℝ) := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  apply mul_nonneg
  · exact Row12.betaDensity_nonneg (by norm_num) (by norm_num) hx.1 hx.2
  · exact Real.rpow_nonneg (le_trans hp.le (functionIntegralBase_lower hp1 hx)) _

/--
@isnad1 id=le.2h1v.s7.0afbb87a6032 from=translated src=- shape=4d18e0ac vocab=eb5c703f
-/
theorem eulerFunctionIntegral_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
      (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) ≤ p ^ (-1 / 6 : ℝ) := by
  have hd : IntervalIntegrable (fun x : ℝ => Row12.betaDensity (5 / 6) x) volume 0 1 := by
    simpa only [pow_zero, one_mul] using
      Row12.betaDensity_moment_integrable (a := (5 / 6 : ℝ)) (by norm_num) (by norm_num) 0
  have hm := intervalIntegral.integral_mono_on zero_le_one
    (eulerFunctionIntegrand_integrable hp hp1) (hd.mul_const (p ^ (-1 / 6 : ℝ)))
    (fun x hx => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hp (functionIntegralBase_lower hp1 hx) (by norm_num))
      (Row12.betaDensity_nonneg (by norm_num) (by norm_num) hx.1 hx.2))
  simpa only [intervalIntegral.integral_mul_const,
    Row12.betaDensity_integral (a := (5 / 6 : ℝ)) (by norm_num) (by norm_num), one_mul] using hm

/--
@isnad1 id=and.2h1v.s8.8a7824e86627 from=translated src=- shape=d0c3006c vocab=eb5c703f
-/
theorem eulerFunctionIntegral_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (0 ≤ ∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
      (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) ∧
    (∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
      (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) ≤ p ^ (-1 / 6 : ℝ) :=
  ⟨eulerFunctionIntegral_nonneg hp hp1, eulerFunctionIntegral_le hp hp1⟩

/--
@isnad1 id=tendsto.0h0v.s7.9dfe4e167a67 from=translated src=- shape=b89ccab8 vocab=f64ffa4a
-/
theorem functionIntegralEndpoint_tendsto :
    Tendsto
      (fun p : ℝ => p * (∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
        (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)))
      (𝓝[Ioi 0] 0) (𝓝 0) := by
  have hp : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0, 0 < p := self_mem_nhdsWithin
  have hp1 : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0, p < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlo : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0,
      0 ≤ p * (∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
        (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) := by
    filter_upwards [hp, hp1] with p hp hp1
    exact mul_nonneg hp.le (eulerFunctionIntegral_nonneg hp hp1)
  have hhi : ∀ᶠ p : ℝ in 𝓝[Ioi 0] 0,
      p * (∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
        (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) ≤ p ^ (5 / 6 : ℝ) := by
    filter_upwards [hp, hp1] with p hp hp1
    calc
      p * (∫ x : ℝ in 0..1, Row12.betaDensity (5 / 6) x *
          (1 - (1 - p) * x) ^ (-1 / 6 : ℝ)) ≤ p * p ^ (-1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left (eulerFunctionIntegral_le hp hp1) hp.le
      _ = p ^ (5 / 6 : ℝ) := by
        rw [show (5 / 6 : ℝ) = 1 + (-1 / 6) by norm_num,
          Real.rpow_add hp, Real.rpow_one]
  exact squeeze_zero' hlo hhi
    (((tendsto_id : Tendsto (fun p : ℝ => p) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).rpow_const_nhds_zero (by norm_num))

end Row12EulerSupport

