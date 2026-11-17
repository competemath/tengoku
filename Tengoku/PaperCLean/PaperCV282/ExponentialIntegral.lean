import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.NumberTheory.Harmonic.EulerMascheroni
import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Convert

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The real exponential integral on the positive half-line

The normalization is Ei(1)=gamma+sum_{n>=1} 1/(n*n!). Integrating exp(t)/t
from 1 gives the standard positive exponential integral. Values at nonpositive
arguments are never used by the saddle endpoints.
-/

namespace PaperC.V282.ExponentialIntegral

open Set Filter Topology MeasureTheory

noncomputable section

def exponentialIntegralAnchor : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 1).factorial : ℝ))

def exponentialIntegral (u : ℝ) : ℝ :=
  exponentialIntegralAnchor + ∫ t in (1 : ℝ)..u, Real.exp t / t

/--
@isnad1 id=summable.0h0v.s6.441dc1b0496d from=translated src=- shape=a0e5b319 vocab=ee9249d4
-/
theorem summable_anchor_series :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) * ((n + 1).factorial : ℝ))) := by
  have hs : Summable (fun n : ℕ => 1 / (n.factorial : ℝ)) := by
    simpa only [one_pow] using Real.summable_pow_div_factorial 1
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  apply one_div_le_one_div_of_le
  · positivity
  · have hfac : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 1)
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    nlinarith [show (0 : ℝ) ≤ ((n + 1).factorial : ℝ) by positivity]

/--
@isnad1 id=eq.0h0v.s3.2a34056af07b from=translated src=- shape=0ae4dc79 vocab=3e64ac2d
-/
theorem exponentialIntegral_one :
    exponentialIntegral 1 = exponentialIntegralAnchor := by
  simp [exponentialIntegral]

/--
@isnad1 id=continuo.1h1v.s5.3ac4c74b8deb from=translated src=- shape=1a6e1fa2 vocab=10a1b29b
-/
theorem continuousOn_integrand {u : ℝ} (hu : 0 < u) :
    ContinuousOn (fun t : ℝ => Real.exp t / t) (uIcc 1 u) := by
  apply Real.continuous_exp.continuousOn.div continuousOn_id
  intro t ht
  have htpos : 0 < t := (lt_min (by norm_num) hu).trans_le ht.1
  exact ne_of_gt htpos

/--
@isnad1 id=interval.1h1v.s5.0ff0b02b4d8d from=translated src=- shape=711a142e vocab=f014c91f
-/
theorem intervalIntegrable_integrand {u : ℝ} (hu : 0 < u) :
    IntervalIntegrable (fun t : ℝ => Real.exp t / t) volume 1 u :=
  (continuousOn_integrand hu).intervalIntegrable

/--
@isnad1 id=hasderiv.1h1v.s5.254f07909c02 from=translated src=- shape=e74d52d9 vocab=2b767868
-/
theorem hasDerivAt_exponentialIntegral {u : ℝ} (hu : 0 < u) :
    HasDerivAt exponentialIntegral (Real.exp u / u) u := by
  have hc : ContinuousAt (fun t : ℝ => Real.exp t / t) u :=
    Real.continuous_exp.continuousAt.div continuousAt_id (ne_of_gt hu)
  have hm : StronglyMeasurableAtFilter (fun t : ℝ => Real.exp t / t) (𝓝 u) :=
    (Real.measurable_exp.div measurable_id).stronglyMeasurable.stronglyMeasurableAtFilter
  exact (intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_integrand hu) hm hc).const_add _

/--
@isnad1 id=continuo.0h0v.s4.685cd4e89918 from=translated src=- shape=f2a09be3 vocab=09a87c6b
-/
theorem continuousOn_exponentialIntegral :
    ContinuousOn exponentialIntegral (Ioi 0) := by
  intro u hu
  exact (hasDerivAt_exponentialIntegral hu).continuousAt.continuousWithinAt

def saddleCostParam (u : ℝ) : ℝ := Real.exp u - exponentialIntegral u

/--
@isnad1 id=hasderiv.1h1v.s6.5f042aee24b9 from=translated src=- shape=acace040 vocab=30a51cc2
-/
theorem hasDerivAt_saddleCostParam {u : ℝ} (hu : 0 < u) :
    HasDerivAt saddleCostParam (Real.exp u * (u - 1) / u) u := by
  change HasDerivAt (fun t => Real.exp t - exponentialIntegral t) _ u
  exact ((Real.hasDerivAt_exp u).sub (hasDerivAt_exponentialIntegral hu)).congr_deriv
    (by field_simp [ne_of_gt hu])

/--
@isnad1 id=continuo.0h0v.s4.a1af495a8779 from=translated src=- shape=f2a09be3 vocab=ac643592
-/
theorem continuousOn_saddleCostParam :
    ContinuousOn saddleCostParam (Ici 1) := by
  intro u hu
  exact (hasDerivAt_saddleCostParam (by linarith [show 1 ≤ u from hu])).continuousAt.continuousWithinAt

/--
@isnad1 id=strictmo.0h0v.s3.6337f8972568 from=translated src=- shape=f2a09be3 vocab=a26e33f1
-/
theorem strictMonoOn_saddleCostParam :
    StrictMonoOn saddleCostParam (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) continuousOn_saddleCostParam
  intro u hu
  have huone : 1 < u := by simpa only [interior_Ici, mem_Ioi] using hu
  rw [(hasDerivAt_saddleCostParam (by linarith)).deriv]
  exact div_pos (mul_pos (Real.exp_pos _) (by linarith)) (by linarith)

/--
@isnad1 id=le.1h1v.s5.3bbbeb958c01 from=translated src=- shape=95abbc82 vocab=94d6090e
-/
theorem one_le_saddleCostParam_deriv {u : ℝ} (hu : 2 ≤ u) :
    1 ≤ Real.exp u * (u - 1) / u := by
  apply (le_div_iff₀ (show 0 < u by linarith)).2
  have hexp := Real.add_one_le_exp u
  have hprod := mul_nonneg (sub_nonneg.2 hexp) (show 0 ≤ u - 1 by linarith)
  nlinarith [sq_nonneg (u - 2)]

/--
@isnad1 id=le.1h1v.s5.a5a9c24bd407 from=translated src=- shape=59a671b7 vocab=f2710be0
-/
theorem saddleCostParam_linear_lower {u : ℝ} (hu : 2 ≤ u) :
    u - 2 + saddleCostParam 2 ≤ saddleCostParam u := by
  have hcont : ContinuousOn saddleCostParam (Ici 2) :=
    continuousOn_saddleCostParam.mono (by intro t ht; exact show 1 ≤ t by linarith [show 2 ≤ t from ht])
  have hdiff : DifferentiableOn ℝ saddleCostParam (interior (Ici 2)) := by
    intro t ht
    have ht2 : 2 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (hasDerivAt_saddleCostParam (by linarith)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Ici (2 : ℝ)), 1 ≤ deriv saddleCostParam t := by
    intro t ht
    have ht2 : 2 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(hasDerivAt_saddleCostParam (by linarith)).deriv]
    exact one_le_saddleCostParam_deriv ht2.le
  have hh := (convex_Ici (2 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderiv 2 (by simp) u hu hu
  linarith

/--
@isnad1 id=tendsto.0h0v.s3.cbe58dd3b912 from=translated src=- shape=41b74a9e vocab=10dc036d
-/
theorem tendsto_saddleCostParam_atTop :
    Tendsto saddleCostParam atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show ∀ᶠ u : ℝ in atTop, u - 2 + saddleCostParam 2 ≤ saddleCostParam u from
      (eventually_ge_atTop 2).mono (fun u hu => saddleCostParam_linear_lower hu))
  simpa only [sub_eq_add_neg, id_eq] using
    tendsto_atTop_add_const_right atTop (saddleCostParam 2)
      (tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_id)

end

end PaperC.V282.ExponentialIntegral
