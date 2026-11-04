module

public import Tengoku.AtPalomar.Paper.RSFunctional
public import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! # The genuine first-moment identity for Parisi CDFs

The identity is an application of Fubini to the measurable triangle `q ≤ t`.
The measures, CDFs, and interval integrals are the actual ones; integrability
is verified before exchanging the order of integration.
-/

open Set MeasureTheory
open scoped Topology ENNReal

namespace Paper

/--
@isnad1 id=interval.0h3v.s4.741c68417d7b from=translated src=- shape=bed93bca vocab=73fee541
-/
theorem parisiCDF_intervalIntegrable (μ : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (parisiCDF μ) volume a b :=
  (parisiCDF_monotone μ).intervalIntegrable

/-- The CDF is the integral of the actual upper-triangle indicator.
@isnad1 id=eq.0h2v.s6.890ccbae188a from=translated src=- shape=8ef1eac1 vocab=a1e4c02f
-/
theorem parisiCDF_eq_integral_upperIndicator (μ : ParisiMeasure) (t : ℝ) :
    parisiCDF μ t = ∫ q : Overlap, if (q : ℝ) ≤ t then (1 : ℝ) else 0
      ∂(μ : Measure Overlap) := by
  have hs : MeasurableSet {q : Overlap | (q : ℝ) ≤ t} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  have hfun : (fun q : Overlap => if (q : ℝ) ≤ t then (1 : ℝ) else 0) =
      Set.indicator {q : Overlap | (q : ℝ) ≤ t} (fun _ => (1 : ℝ)) := by
    funext q
    simp only [Set.indicator, mem_ofPred_eq]
  rw [hfun, integral_indicator hs]
  simp only [parisiCDF, setIntegral_const, smul_eq_mul, mul_one, Measure.real]

/-- Each vertical section of the upper triangle has length `1-q`.
@isnad1 id=eq.1h1v.s6.ab8d664fdbae from=translated src=- shape=5db8ff95 vocab=7894f006
-/
theorem integral_upperIndicator (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, if q ≤ t then (1 : ℝ) else 0) = 1 - q := by
  let f : ℝ → ℝ := fun t => if q ≤ t then 1 else 0
  have heq0 : EqOn f (fun _ => (0 : ℝ)) (uIoo 0 q) := by
    intro t ht
    rw [uIoo_of_le hq.1] at ht
    simp [f, not_le_of_gt ht.2]
  have heq1 : EqOn f (fun _ => (1 : ℝ)) (uIoo q 1) := by
    intro t ht
    rw [uIoo_of_le hq.2] at ht
    simp [f, ht.1.le]
  have hInt0 : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_congr_uIoo heq0).mpr intervalIntegrable_const
  have hInt1 : IntervalIntegrable f volume q 1 :=
    (intervalIntegrable_congr_uIoo heq1).mpr intervalIntegrable_const
  have h0 : (∫ t in (0 : ℝ)..q, f t) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo heq0]
    simp
  have h1 : (∫ t in q..(1 : ℝ), f t) = 1 - q := by
    rw [intervalIntegral.integral_congr_uIoo heq1]
    simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1
  change (∫ t in (0 : ℝ)..1, f t) = 1 - q
  rw [h0, h1, zero_add] at hadd
  exact hadd.symm

/-- Exact CDF first-moment identity for every actual probability measure on
the overlap interval. It includes arbitrary atoms and singular measures.
@isnad1 id=eq.0h1v.s6.f6ba3ed8da6f from=translated src=- shape=6471dab1 vocab=7b2755b1
-/
theorem parisiCDF_integral_eq_firstMoment (μ : ParisiMeasure) :
    (∫ t in (0 : ℝ)..1, parisiCDF μ t) =
      ∫ q : Overlap, 1 - (q : ℝ) ∂(μ : Measure Overlap) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hset : MeasurableSet {p : ℝ × Overlap | (p.2 : ℝ) ≤ p.1} :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_fst).measurableSet
  have hm : Measurable (fun p : ℝ × Overlap =>
      if (p.2 : ℝ) ≤ p.1 then (1 : ℝ) else 0) := by
    exact measurable_const.ite hset measurable_const
  have hF : Integrable (fun p : ℝ × Overlap =>
      if (p.2 : ℝ) ≤ p.1 then (1 : ℝ) else 0)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (μ : Measure Overlap)) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards with p
    split <;> norm_num
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp_rw [parisiCDF_eq_integral_upperIndicator μ]
  rw [integral_integral_swap hF]
  apply integral_congr_ae
  filter_upwards with q
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integral_upperIndicator (q : ℝ) q.2

/--
@isnad1 id=interval.0h4v.s5.c6de00fc73ec from=translated src=- shape=d139fc39 vocab=9ccbb11e
-/
theorem parisiCDF_abs_diff_intervalIntegrable (μ ν : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (fun t => |parisiCDF μ t - parisiCDF ν t|) volume a b :=
  ((parisiCDF_intervalIntegrable μ a b).sub (parisiCDF_intervalIntegrable ν a b)).abs

end Paper
