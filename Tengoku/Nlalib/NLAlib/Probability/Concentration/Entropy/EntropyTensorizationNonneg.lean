import Tengoku.Nlalib.NLAlib.Probability.Concentration.Entropy.EntropyTensorization
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Real
import Tengoku.Seed.Analysis.Convex.Integral
import Tengoku.Seed.Analysis.SpecialFunctions.Log.NegMulLog
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.IntegralUpdate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Entropy tensorization for nonnegative functions

Atlas: `entropy-tensorization`. Extends Ledoux, Prop. 5.6 and
Boucheron--Lugosi--Massart 2013, Thm. 4.10 from positive to nonnegative
functions, retaining NLAlib's literal entropy expression. The proof uses
Mathlib's Jensen inequality for `x log x`, one-coordinate conditional means,
and the uniform regularization bound already in NLAlib.

The local registry at `E:/Database-RA01-reviewed-2026-10-06` was consulted:
the conditional-mean coupling of `PP-03/T-0027` is restricted to signed
bucket selectors and is not used as an arbitrary-measure entropy theorem.
No registry claim is promoted or used beyond its recorded scope.
-/

noncomputable section
open MeasureTheory Filter

namespace NLAlib

/-- Integrability of a nonnegative function follows from integrability of
`f log f` on a finite measure space. Source: Mathlib's
`Real.self_sub_one_le_mul_log`. Atlas: `entropy-tensorization`.
@isnad1 id=integrab.3h3v.s6.bbd6e5f6272d from=translated src=- shape=70d8ef38 vocab=8cf78e15
-/
theorem integrable_of_nonneg_mul_log_integrable {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hlog : Integrable (fun x => f x * Real.log (f x)) ν) :
    Integrable f ν := by
  refine Integrable.mono' (hlog.abs.add (integrable_const (1 : ℝ)))
    hfm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (hf x)]
  have h := Real.self_sub_one_le_mul_log (hf x)
  have ha := le_abs_self (f x * Real.log (f x))
  linarith

/-- Jensen's inequality for `x log x`, with zero values allowed. Source:
Mathlib's `Real.convexOn_mul_log` and `ConvexOn.map_integral_le`.
Atlas: `entropy-tensorization`.
@isnad1 id=le.3h3v.s7.0fcbf0111463 from=translated src=- shape=e5c90681 vocab=1f6e985d
-/
theorem mul_log_integral_le_integral_mul_log_of_nonneg {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hint : Integrable f ν)
    (hlog : Integrable (fun x => f x * Real.log (f x)) ν) :
    (∫ x, f x ∂ν) * Real.log (∫ x, f x ∂ν) ≤ ∫ x, f x * Real.log (f x) ∂ν :=
  Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici (ae_of_all _ fun x => hf x) hint hlog

/-- Positive regularization preserves integrability of `f log f`, with a
dominating function independent of `0 < δ ≤ 1`. Source: NLAlib's
`abs_add_mul_log_add_le`. Atlas: `entropy-tensorization`.
@isnad1 id=integrab.6h4v.s7.1b44c24d75ec from=translated src=- shape=1e324f89 vocab=1eb05853
-/
theorem integrable_mul_log_add_of_nonneg {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hint : Integrable f ν)
    (hlog : Integrable (fun x => f x * Real.log (f x)) ν)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (fun x => (f x + δ) * Real.log (f x + δ)) ν := by
  refine Integrable.mono' ((hlog.abs.add hint).add (integrable_const (2 : ℝ)))
    (Real.continuous_mul_log.measurable.comp (hfm.add measurable_const)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  exact abs_add_mul_log_add_le (f x) δ (hf x) hδ hδ1

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]

/-- `E_i f log(E_i f)` is integrable whenever a nonnegative `f` and its
entropy integrand are integrable. The proof uses conditional Jensen and
the lower bound `x log x ≥ -1`. Source: Jensen's inequality and NLAlib's
one-coordinate Fubini lemmas. Atlas: `entropy-tensorization`.
@isnad1 id=integrab.4h5v.s8.c991ff15edb1 from=translated src=- shape=b4aea03b vocab=c31d48dc
-/
theorem integrable_mul_log_integral_update_of_nonneg (i : ι)
    {f : (ι → Ω) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f (Measure.pi μ))
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    Integrable (fun x => (∫ t, f (Function.update x i t) ∂(μ i)) *
      Real.log (∫ t, f (Function.update x i t) ∂(μ i))) (Measure.pi μ) := by
  have hmeas := measurable_integral_update_pi μ i hfm
  have hupper := integrable_integral_update_pi μ i hlog
  refine Integrable.mono' (hupper.abs.add (integrable_const (1 : ℝ)))
    (Real.continuous_mul_log.measurable.comp hmeas).aestronglyMeasurable ?_
  filter_upwards [ae_integrable_comp_update_pi μ i hint,
    ae_integrable_comp_update_pi μ i hlog] with x h1 h2
  have hu := mul_log_integral_le_integral_mul_log_of_nonneg
    (fun t => hf (Function.update x i t)) h1 h2
  have hm0 : 0 ≤ ∫ t, f (Function.update x i t) ∂(μ i) :=
    integral_nonneg fun t => hf _
  have hl := Real.self_sub_one_le_mul_log hm0
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · have ha := abs_nonneg (∫ t,
      f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i))
    linarith
  · have ha := le_abs_self (∫ t,
      f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i))
    linarith

/-- The actual one-coordinate entropy is integrable, also when `f` has
zeros. Source: conditional Jensen and one-coordinate Fubini.
Atlas: `entropy-tensorization`.
@isnad1 id=integrab.4h5v.s8.677f38023bdf from=translated src=- shape=fe7c60fc vocab=07604dd0
-/
theorem integrable_entropy_update_of_nonneg (i : ι) {f : (ι → Ω) → ℝ}
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f (Measure.pi μ))
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    Integrable (fun x => (∫ t,
      f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i)) -
        (∫ t, f (Function.update x i t) ∂(μ i)) *
          Real.log (∫ t, f (Function.update x i t) ∂(μ i))) (Measure.pi μ) :=
  (integrable_integral_update_pi μ i hlog).sub
    (integrable_mul_log_integral_update_of_nonneg μ i hfm hf hint hlog)

/-- Integrated local entropy equals global `E[f log f]` minus the entropy
integrand of the conditional mean. All integrability requirements are
proved from the nonnegative-function hypotheses. Source: conditional
Jensen and one-coordinate Fubini. Atlas: `entropy-tensorization`.
@isnad1 id=eq.4h5v.s8.450389f47e27 from=translated src=- shape=16009e21 vocab=07604dd0
-/
theorem integral_entropy_update_eq_sub_integral_mul_log_mean (i : ι)
    {f : (ι → Ω) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f (Measure.pi μ))
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    (∫ x, ((∫ t, f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i)) -
      (∫ t, f (Function.update x i t) ∂(μ i)) *
        Real.log (∫ t, f (Function.update x i t) ∂(μ i))) ∂(Measure.pi μ)) =
      (∫ x, f x * Real.log (f x) ∂(Measure.pi μ)) -
        ∫ x, (∫ t, f (Function.update x i t) ∂(μ i)) *
          Real.log (∫ t, f (Function.update x i t) ∂(μ i)) ∂(Measure.pi μ) := by
  rw [integral_sub (integrable_integral_update_pi μ i hlog)
    (integrable_mul_log_integral_update_of_nonneg μ i hfm hf hint hlog),
    integral_integral_update_pi μ i hlog]

end Product
end NLAlib
