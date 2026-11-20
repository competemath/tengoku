import Tengoku.Lmlf.LMLF.Integral.Improper.Abel
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.MeasureTheory.Integral.ExpDecay
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Analytic Abel regressions for IMP-001.

These source-free, nonpublic examples use only the public IMP API.
-/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace LMLFTest.Integral.Improper

open LMLF.Integral

/-- The zero integrand in the discontinuous-primitive counterexample.-/
def gJ (_t : ℝ) : ℝ := 0

/-- The exact step specified by REG.6, with value zero at one.-/
def FJ (t : ℝ) : ℝ := if t ≤ 1 then 0 else 1

/-- The zero integrand in the endpoint-only counterexample.-/
def gB (_t : ℝ) : ℝ := 0

/-- The compact polynomial bump specified by REG.7.-/
def FB (t : ℝ) : ℝ :=
  if 0 ≤ t ∧ t ≤ 1 then t * (1 - t) else 0

/-- The closed-interval indicator specified by REG.8, including both endpoints.-/
def gI (t : ℝ) : ℝ := if 1 ≤ t ∧ t ≤ 2 then 1 else 0

/-- The clipped primitive specified by REG.8.-/
def FI (t : ℝ) : ℝ := min (max (t - 1) 0) 1

private theorem zero_improper (k : ℝ) (S : Finset ℝ)
    (hS : ∀ c ∈ S, k < c) :
    HasImproperIntegralAtTopExcept (fun _ : ℝ => (0 : ℝ)) k S (0 : ℝ) := by
  apply hasImproperIntegralAtTopExcept_iff_exists_primitive.mpr
  refine ⟨fun _ : ℝ => (0 : ℝ), ⟨hS, continuous_const.continuousOn, rfl, ?_⟩,
    tendsto_const_nhds⟩
  intro a b _ _ _
  exact ⟨intervalIntegrable_const, by simp⟩

private theorem weightedFJ_eq_indicator :
    (fun t : ℝ => Real.exp (-t) * FJ t) =
      (Ioi (1 : ℝ)).indicator (fun t => Real.exp (-t)) := by
  funext t
  by_cases ht : t ≤ 1
  · simp [FJ, ht, not_lt.mpr ht]
  · simp [FJ, ht, lt_of_not_ge ht]

private theorem weightedFJ_integrable :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * FJ t) (Ioi 0) := by
  rw [weightedFJ_eq_indicator]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using exp_neg_integrableOn_Ioi 0 zero_lt_one
  exact hexp.indicator measurableSet_Ioi

private theorem weightedFJ_integral :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t) * FJ t = Real.exp (-1) := by
  rw [weightedFJ_eq_indicator, MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  have hset : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := by ext t; simp
  rw [hset, integral_exp_neg_Ioi]

private theorem weightedFJ_tendsto :
    Tendsto (fun R : ℝ => Real.exp (-R) * FJ R) atTop (nhds 0) := by
  have hexp : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  simp [FJ, not_le.mpr hR]

private theorem FJ_not_continuousOn : ¬ ContinuousOn FJ (Ici 0) := by
  intro hcont
  have hnhds : Ici (0 : ℝ) ∈ nhds (1 : ℝ) :=
    mem_of_superset (Ioi_mem_nhds zero_lt_one) Ioi_subset_Ici_self
  have hca : ContinuousAt FJ 1 := (hcont 1 (by norm_num)).continuousAt hnhds
  rw [Metric.continuousAt_iff] at hca
  rcases hca (1 / 2 : ℝ) (by norm_num) with ⟨δ, hδ, hbound⟩
  let y : ℝ := 1 + δ / 2
  have hy : 1 < y := by dsimp [y]; linarith
  have hydist : dist y 1 < δ := by
    rw [Real.dist_eq]
    dsimp [y]
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have := hbound hydist
  simp [FJ, not_le.mpr hy] at this
  norm_num at this

/-- IMP-R11: all componentwise primitive fields except continuity hold, while
the Abel value is wrong by the strictly positive jump `exp (-1)`.
@isnad1 id=and.0h0v.s9.26882acc0141 from=translated src=- shape=04bed9ee vocab=67a5bfbb
-/
theorem discontinuousPrimitive_counterexample :
    (∀ c ∈ ({1} : Finset ℝ), (0 : ℝ) < c) ∧
      FJ 0 = 0 ∧
      (∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
        Disjoint (Icc a b) (↑({1} : Finset ℝ) : Set ℝ) →
          IntervalIntegrable gJ volume a b ∧
            FJ b - FJ a = ∫ t in a..b, gJ t) ∧
      ¬ ContinuousOn FJ (Ici 0) ∧
      IntegrableOn (fun t : ℝ => Real.exp (-t) * FJ t) (Ioi 0) ∧
      Tendsto (fun R : ℝ => Real.exp (-R) * FJ R) atTop (nhds 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * FJ t) = Real.exp (-1) ∧
      0 < Real.exp (-1) ∧
      HasImproperIntegralAtTopExcept
        (fun t : ℝ => Real.exp (-t) * gJ t) 0 {1} 0 ∧
      (∀ I : ℝ, HasImproperIntegralAtTopExcept
        (fun t : ℝ => Real.exp (-t) * gJ t) 0 {1} I ↔ I = 0) ∧
      ¬ HasImproperIntegralAtTopExcept
        (fun t : ℝ => Real.exp (-t) * gJ t) 0 {1} (Real.exp (-1)) := by
  have hS : ∀ c ∈ ({1} : Finset ℝ), (0 : ℝ) < c := by simp
  have hzero : HasImproperIntegralAtTopExcept
      (fun _ : ℝ => (0 : ℝ)) 0 {1} 0 := zero_improper 0 {1} hS
  have hwzero : HasImproperIntegralAtTopExcept
      (fun t : ℝ => Real.exp (-t) * gJ t) 0 {1} 0 := by
    simpa [gJ] using hzero
  refine ⟨hS, by simp [FJ], ?_, FJ_not_continuousOn,
    weightedFJ_integrable, weightedFJ_tendsto, weightedFJ_integral,
    Real.exp_pos _, hwzero, ?_, ?_⟩
  · intro a b ha hab hdisj
    refine ⟨by
      change IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b
      exact intervalIntegrable_const, ?_⟩
    have hone : (1 : ℝ) ∉ Icc a b := by
      intro hmem
      exact Set.disjoint_left.1 hdisj hmem (by simp)
    have hside : b < 1 ∨ 1 < a := by
      by_cases hb : b < 1
      · exact Or.inl hb
      · right
        have h1b : 1 ≤ b := le_of_not_gt hb
        by_contra hna
        exact hone ⟨le_of_not_gt hna, h1b⟩
    rcases hside with hb | ha1
    · simp [FJ, gJ, hb.le, (hab.trans_lt hb).le]
    · simp [FJ, gJ, not_le.mpr ha1, not_le.mpr (ha1.trans_le hab)]
  · intro I
    constructor
    · intro hI
      exact HasImproperIntegralAtTopExcept.unique hI hwzero
    · rintro rfl
      exact hwzero
  · intro hbad
    have := HasImproperIntegralAtTopExcept.unique hbad hwzero
    exact (Real.exp_ne_zero (-1)) this

private theorem FB_eq_max (t : ℝ) : FB t = max (t * (1 - t)) 0 := by
  by_cases h0 : 0 ≤ t
  · by_cases h1 : t ≤ 1
    · simp [FB, h0, h1, max_eq_left (mul_nonneg h0 (sub_nonneg.mpr h1))]
    · have hp : t * (1 - t) ≤ 0 := by nlinarith
      simp [FB, h0, h1, max_eq_right hp]
  · have hp : t * (1 - t) ≤ 0 := by nlinarith
    simp [FB, h0, max_eq_right hp]

private theorem FB_continuous : Continuous FB := by
  rw [show FB = fun t : ℝ => max (t * (1 - t)) 0 by
    funext t
    exact FB_eq_max t]
  fun_prop

private theorem FB_nonneg (t : ℝ) : 0 ≤ FB t := by
  rw [FB_eq_max]
  exact le_max_right _ _

private theorem FB_le_one (t : ℝ) : FB t ≤ 1 := by
  simp only [FB]
  split_ifs with ht
  · nlinarith [sq_nonneg (t - 1 / 2)]
  · norm_num

private theorem weightedFB_integrable {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun t : ℝ => Real.exp (-h * t) * FB t) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-h * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hh
  refine hexp.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul FB_continuous).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (FB_nonneg t))]
    nlinarith [FB_le_one t, Real.exp_pos (-h * t)]

private theorem weightedFB_integral_eq_interval (h : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FB t) =
      ∫ t in (0 : ℝ)..1, Real.exp (-h * t) * FB t := by
  let q : ℝ → ℝ := fun t => Real.exp (-h * t) * FB t
  have hq : q = (Icc (0 : ℝ) 1).indicator q := by
    funext t
    by_cases ht : 0 ≤ t ∧ t ≤ 1
    · simp [q, ht]
    · simp [q, FB, ht]
  change (∫ t in Ioi (0 : ℝ), q t) = ∫ t in (0 : ℝ)..1, q t
  calc
    (∫ t in Ioi (0 : ℝ), q t) =
        ∫ t in Ioi (0 : ℝ), (Icc (0 : ℝ) 1).indicator q t := by rw [← hq]
    _ = ∫ t in Ioi (0 : ℝ) ∩ Icc 0 1, q t :=
      MeasureTheory.setIntegral_indicator measurableSet_Icc
    _ = ∫ t in Ioc (0 : ℝ) 1, q t := by
      rw [show Ioi (0 : ℝ) ∩ Icc 0 1 = Ioc 0 1 by
      ext t
      constructor
      · rintro ⟨ht0, _ht0', ht1⟩
        exact ⟨ht0, ht1⟩
      · rintro ⟨ht0, ht1⟩
        exact ⟨ht0, ht0.le, ht1⟩]
    _ = ∫ t in (0 : ℝ)..1, q t :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

private theorem weightedFB_integral_pos {h : ℝ} (hh : 0 < h) :
    0 < ∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FB t := by
  have hint := weightedFB_integrable hh
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (FB_nonneg t)) hint).2
  have hsubset : Ioo (0 : ℝ) 1 ⊆
      Function.support (fun t : ℝ => Real.exp (-h * t) * FB t) ∩ Ioi 0 := by
    intro t ht
    refine ⟨?_, ht.1⟩
    rw [Function.mem_support]
    have hFB : 0 < FB t := by
      have hbounds : 0 ≤ t ∧ t ≤ 1 := ⟨ht.1.le, ht.2.le⟩
      rw [FB, ite_eq_left hbounds]
      exact mul_pos ht.1 (sub_pos.mpr ht.2)
    exact ne_of_gt (mul_pos (Real.exp_pos _) hFB)
  calc
    0 < volume (Ioo (0 : ℝ) 1) := by simp
    _ ≤ volume
        (Function.support (fun t : ℝ => Real.exp (-h * t) * FB t) ∩ Ioi 0) :=
      measure_mono hsubset

/-- IMP-R12: endpoint matching for the compact bump does not imply the
all-intermediate increment law, and every positive Abel weight detects it.
@isnad1 id=and.0h0v.s9.c23f8d6467ef from=translated src=- shape=1f239fbf vocab=9567602f
-/
theorem endpointOnly_counterexample :
    Continuous FB ∧ FB 0 = 0 ∧ FB 1 = 0 ∧
      FB 1 - FB 0 = ∫ t in (0 : ℝ)..1, gB t ∧
      FB (1 / 2) - FB 0 ≠ ∫ t in (0 : ℝ)..(1 / 2), gB t ∧
      (∀ h : ℝ, 0 < h →
        IntegrableOn (fun t : ℝ => Real.exp (-h * t) * FB t) (Ioi 0) ∧
        0 < ∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FB t ∧
        0 < h * ∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FB t ∧
        (∫ t in (0 : ℝ)..1, Real.exp (-h * t) * gB t) = 0 ∧
        (∫ t in (0 : ℝ)..1, Real.exp (-h * t) * gB t) ≠
          Real.exp (-h * 1) * FB 1 - Real.exp (-h * 0) * FB 0 +
            h * ∫ t in (0 : ℝ)..1, Real.exp (-h * t) * FB t) := by
  refine ⟨FB_continuous, by simp [FB], by simp [FB], ?_, ?_, ?_⟩
  · simp [FB, gB]
  · norm_num [FB, gB]
  · intro h hh
    have hpos := weightedFB_integral_pos hh
    have hposInterval :
        0 < ∫ t in (0 : ℝ)..1, Real.exp (-h * t) * FB t := by
      rwa [weightedFB_integral_eq_interval] at hpos
    refine ⟨weightedFB_integrable hh, hpos, mul_pos hh hpos, by simp [gB], ?_⟩
    have hrhs :
        Real.exp (-h * 1) * FB 1 - Real.exp (-h * 0) * FB 0 +
            h * ∫ t in (0 : ℝ)..1, Real.exp (-h * t) * FB t =
          h * ∫ t in (0 : ℝ)..1, Real.exp (-h * t) * FB t := by
      norm_num [FB]
    rw [show (∫ t in (0 : ℝ)..1, Real.exp (-h * t) * gB t) = 0 by simp [gB],
      hrhs]
    exact (ne_of_gt (mul_pos hh hposInterval)).symm

private theorem gI_eq_indicator :
    gI = (Icc (1 : ℝ) 2).indicator (fun _ : ℝ => (1 : ℝ)) := by
  funext t
  simp only [gI, Set.indicator, mem_Icc]

private theorem FI_of_le_one {t : ℝ} (ht : t ≤ 1) : FI t = 0 := by
  simp [FI, max_eq_right (sub_nonpos.mpr ht)]

private theorem FI_of_mem_Icc {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    FI t = t - 1 := by
  rw [FI, max_eq_left (sub_nonneg.mpr ht1), min_eq_left]
  linarith

private theorem FI_of_two_le {t : ℝ} (ht : 2 ≤ t) : FI t = 1 := by
  rw [FI, max_eq_left (by linarith), min_eq_right]
  linarith

private theorem gI_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable gI volume a b := by
  rw [gI_eq_indicator]
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 1 2) :=
    integrableOn_const measure_Icc_lt_top.ne
  exact (hconst.integrable_indicator measurableSet_Icc).intervalIntegrable

private theorem integral_gI_eq (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, gI t) = FI b - FI a := by
  rw [intervalIntegral.integral_of_le hab, gI_eq_indicator,
    MeasureTheory.setIntegral_indicator measurableSet_Icc]
  simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  by_cases hb1 : b ≤ 1
  · rw [FI_of_le_one hb1, FI_of_le_one (hab.trans hb1), sub_self]
    have hnull : volume (Ioc a b ∩ Icc (1 : ℝ) 2) = 0 := by
      apply measure_mono_null (t := {1})
      · intro t ht
        have htb := ht.1.2
        have h1t := ht.2.1
        simp only [mem_singleton_iff]
        linarith
      · simp
    simp [Measure.real, hnull]
  · have h1b : 1 < b := lt_of_not_ge hb1
    by_cases ha2 : 2 ≤ a
    · rw [FI_of_two_le ha2, FI_of_two_le (ha2.trans hab), sub_self]
      have hempty : Ioc a b ∩ Icc (1 : ℝ) 2 = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_Ioc, mem_Icc, mem_empty_iff_false, iff_false]
        intro ht
        linarith
      simp [hempty]
    · have ha2' : a < 2 := lt_of_not_ge ha2
      by_cases ha1 : a < 1
      · by_cases hb2 : b ≤ 2
        · rw [FI_of_mem_Icc h1b.le hb2, FI_of_le_one ha1.le]
          have hset : Ioc a b ∩ Icc (1 : ℝ) 2 = Icc 1 b := by
            ext t
            simp only [mem_inter_iff, mem_Ioc, mem_Icc]
            constructor <;> intro ht
            · exact ⟨ht.2.1, ht.1.2⟩
            · exact ⟨⟨ha1.trans_le ht.1, ht.2⟩, ht.1, ht.2.trans hb2⟩
          rw [hset]
          simp [h1b.le]
        · have h2b : 2 < b := lt_of_not_ge hb2
          rw [FI_of_two_le h2b.le, FI_of_le_one ha1.le]
          have hset : Ioc a b ∩ Icc (1 : ℝ) 2 = Icc 1 2 := by
            ext t
            simp only [mem_inter_iff, mem_Ioc, mem_Icc]
            constructor <;> intro ht
            · exact ht.2
            · exact ⟨⟨ha1.trans_le ht.1, ht.2.trans h2b.le⟩, ht⟩
          rw [hset]
          norm_num [Real.volume_Icc]
      · have h1a : 1 ≤ a := le_of_not_gt ha1
        by_cases hb2 : b ≤ 2
        · rw [FI_of_mem_Icc (h1a.trans hab) hb2, FI_of_mem_Icc h1a ha2'.le]
          have hset : Ioc a b ∩ Icc (1 : ℝ) 2 = Ioc a b := by
            ext t
            simp only [mem_inter_iff, mem_Ioc, mem_Icc]
            constructor <;> intro ht
            · exact ht.1
            · exact ⟨ht, h1a.trans ht.1.le, ht.2.trans hb2⟩
          rw [hset]
          simp [sub_nonneg.mpr hab]
        · have h2b : 2 < b := lt_of_not_ge hb2
          rw [FI_of_two_le h2b.le, FI_of_mem_Icc h1a ha2'.le]
          have hset : Ioc a b ∩ Icc (1 : ℝ) 2 = Ioc a 2 := by
            ext t
            simp only [mem_inter_iff, mem_Ioc, mem_Icc]
            constructor <;> intro ht
            · exact ⟨ht.1.1, ht.2.2⟩
            · exact ⟨⟨ht.1, ht.2.trans h2b.le⟩, h1a.trans ht.1.le, ht.2⟩
          rw [hset]
          simp [sub_nonneg.mpr ha2'.le]
          ring

private theorem FI_continuous : Continuous FI := by
  exact (((continuous_id.sub continuous_const).max continuous_const).min continuous_const)

private theorem FI_nonneg (t : ℝ) : 0 ≤ FI t := by
  exact le_min (le_max_right _ _) zero_le_one

private theorem FI_le_one (t : ℝ) : FI t ≤ 1 := min_le_right _ _

private theorem indicatorPrimitive : IsFiniteExceptionalPrimitive gI 0 ∅ FI := by
  refine ⟨by simp, FI_continuous.continuousOn, by norm_num [FI], ?_⟩
  intro a b _ha hab _
  exact ⟨gI_intervalIntegrable a b, (integral_gI_eq a b hab).symm⟩

private theorem FI_not_differentiableAt_one : ¬ DifferentiableAt ℝ FI 1 := by
  intro hdiff
  have hfullRight : HasDerivWithinAt FI (deriv FI 1) (Icc (1 : ℝ) 2) 1 :=
    hdiff.hasDerivAt.hasDerivWithinAt
  have hfullLeft : HasDerivWithinAt FI (deriv FI 1) (Icc (0 : ℝ) 1) 1 :=
    hdiff.hasDerivAt.hasDerivWithinAt
  have hright : HasDerivWithinAt FI 1 (Icc (1 : ℝ) 2) 1 := by
    exact (((hasDerivAt_id (1 : ℝ)).sub_const 1).hasDerivWithinAt).congr_of_mem
      (fun t ht => FI_of_mem_Icc ht.1 ht.2) (by simp)
  have hleft : HasDerivWithinAt FI 0 (Icc (0 : ℝ) 1) 1 := by
    exact (hasDerivAt_const (x := (1 : ℝ)) (c := (0 : ℝ))).hasDerivWithinAt.congr_of_mem
      (fun t ht => FI_of_le_one ht.2) (by simp)
  have hd1 := (uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2)).eq
    (by simp : (1 : ℝ) ∈ Icc 1 2) hfullRight hright
  have hd0 := (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)).eq
    (by simp : (1 : ℝ) ∈ Icc 0 1) hfullLeft hleft
  rw [hd1] at hd0
  have hcontra := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd0
  norm_num at hcontra

private theorem FI_not_differentiableAt_two : ¬ DifferentiableAt ℝ FI 2 := by
  intro hdiff
  have hfullLeft : HasDerivWithinAt FI (deriv FI 2) (Icc (1 : ℝ) 2) 2 :=
    hdiff.hasDerivAt.hasDerivWithinAt
  have hfullRight : HasDerivWithinAt FI (deriv FI 2) (Icc (2 : ℝ) 3) 2 :=
    hdiff.hasDerivAt.hasDerivWithinAt
  have hleft : HasDerivWithinAt FI 1 (Icc (1 : ℝ) 2) 2 := by
    exact (((hasDerivAt_id (2 : ℝ)).sub_const 1).hasDerivWithinAt).congr_of_mem
      (fun t ht => FI_of_mem_Icc ht.1 ht.2) (by simp)
  have hright : HasDerivWithinAt FI 0 (Icc (2 : ℝ) 3) 2 := by
    exact (hasDerivAt_const (x := (2 : ℝ)) (c := (1 : ℝ))).hasDerivWithinAt.congr_of_mem
      (fun t ht => FI_of_two_le ht.1) (by norm_num)
  have hd1 := (uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2)).eq
    (by simp : (2 : ℝ) ∈ Icc 1 2) hfullLeft hleft
  have hd0 := (uniqueDiffOn_Icc (by norm_num : (2 : ℝ) < 3)).eq
    (by norm_num : (2 : ℝ) ∈ Icc 2 3) hfullRight hright
  rw [hd1] at hd0
  have hcontra := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd0
  norm_num at hcontra

private theorem weightedFI_integrable {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun t : ℝ => Real.exp (-h * t) * FI t) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-h * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hh
  refine hexp.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul FI_continuous).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (FI_nonneg t))]
    nlinarith [FI_le_one t, Real.exp_pos (-h * t)]

private theorem exp_neg_mul_tendsto_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℝ => Real.exp (-h * t)) atTop (nhds 0) := by
  have hscale : Tendsto (fun t : ℝ => h * t) atTop atTop :=
    tendsto_id.const_mul_atTop hh
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).congr' ?_
  exact Eventually.of_forall fun t => by simp only [Function.comp_apply, neg_mul]

private theorem weightedFI_tendsto {h : ℝ} (hh : 0 < h) :
    Tendsto (fun R : ℝ => Real.exp (-h * R) * FI R) atTop (nhds 0) := by
  refine (exp_neg_mul_tendsto_zero hh).congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  rw [FI_of_two_le hR, mul_one]

private theorem weightedgI_eq_indicator (h : ℝ) :
    (fun t : ℝ => Real.exp (-h * t) * gI t) =
      (Icc (1 : ℝ) 2).indicator (fun t => Real.exp (-h * t)) := by
  funext t
  by_cases ht : 1 ≤ t ∧ t ≤ 2
  · simp [gI, ht]
  · simp [gI, ht]

private theorem weightedgI_integrable {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun t : ℝ => Real.exp (-h * t) * gI t) (Ioi 0) := by
  rw [weightedgI_eq_indicator]
  exact (exp_neg_integrableOn_Ioi 0 hh).indicator measurableSet_Icc

private theorem weightedgI_integral {h : ℝ} (hh : 0 < h) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * gI t) =
      (Real.exp (-h) - Real.exp (-2 * h)) / h := by
  rw [weightedgI_eq_indicator, MeasureTheory.setIntegral_indicator measurableSet_Icc]
  have hset : Ioi (0 : ℝ) ∩ Icc 1 2 = Icc 1 2 := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Icc]
    constructor
    · exact fun ht => ht.2
    · exact fun ht => ⟨zero_lt_one.trans_le ht.1, ht⟩
  rw [hset, MeasureTheory.setIntegral_congr_set
    (Ioc_ae_eq_Icc (a := (1 : ℝ)) (b := 2)).symm]
  rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have hexp1 : IntegrableOn (fun t : ℝ => Real.exp (-h * t)) (Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 hh
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hexp1 (by norm_num : (1 : ℝ) ≤ 2)]
  rw [integral_exp_mul_Ioi (a := -h) (neg_lt_zero.mpr hh) 1,
    integral_exp_mul_Ioi (a := -h) (neg_lt_zero.mpr hh) 2]
  field_simp [ne_of_gt hh]

private theorem weightedFI_middle_integral {h : ℝ} (hh : 0 < h) :
    (∫ t in (1 : ℝ)..2, Real.exp (-h * t) * FI t) =
      Real.exp (-h) / h ^ 2 - Real.exp (-2 * h) / h -
        Real.exp (-2 * h) / h ^ 2 := by
  let A : ℝ → ℝ := fun t =>
    -Real.exp (-h * t) * ((t - 1) / h + 1 / h ^ 2)
  have hA (t : ℝ) : HasDerivAt A (Real.exp (-h * t) * (t - 1)) t := by
    have hE : HasDerivAt (fun x : ℝ => Real.exp (-h * x))
        (-h * Real.exp (-h * t)) t := by
      simpa only [id_eq, neg_mul, mul_one, mul_neg, mul_comm] using
        ((hasDerivAt_id t).const_mul (-h)).exp
    have hB : HasDerivAt (fun x : ℝ => (x - 1) / h + 1 / h ^ 2) (1 / h) t := by
      simpa using (((hasDerivAt_id t).sub_const 1).div_const h).add_const (1 / h ^ 2)
    convert! hE.neg.mul hB using 1
    field_simp [ne_of_gt hh]
    simp only [Pi.neg_apply]
    ring
  have hInt : IntervalIntegrable
      (fun t : ℝ => Real.exp (-h * t) * (t - 1)) volume 1 2 := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.sub continuous_const)).intervalIntegrable 1 2
  have hFTC :
      (∫ t in (1 : ℝ)..2, Real.exp (-h * t) * (t - 1)) = A 2 - A 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
      (by fun_prop) (fun t _ => hA t) hInt
  have hcongr :
      (∫ t in (1 : ℝ)..2, Real.exp (-h * t) * FI t) =
        ∫ t in (1 : ℝ)..2, Real.exp (-h * t) * (t - 1) :=
    intervalIntegral.integral_congr (by
    intro t ht
    have ht' : t ∈ Icc (1 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using ht
    change Real.exp (-h * t) * FI t = Real.exp (-h * t) * (t - 1)
    rw [FI_of_mem_Icc ht'.1 ht'.2])
  rw [hcongr, hFTC]
  dsimp only [A]
  field_simp [ne_of_gt hh]
  ring

private theorem weightedFI_tail_integral {h : ℝ} (hh : 0 < h) :
    (∫ t in Ioi (2 : ℝ), Real.exp (-h * t) * FI t) =
      Real.exp (-2 * h) / h := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
    rw [FI_of_two_le ht.le, mul_one])]
  rw [integral_exp_mul_Ioi (a := -h) (neg_lt_zero.mpr hh) 2]
  field_simp [ne_of_gt hh]

private theorem weightedFI_integral {h : ℝ} (hh : 0 < h) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FI t) =
      (Real.exp (-h) - Real.exp (-2 * h)) / h ^ 2 := by
  let q : ℝ → ℝ := fun t => Real.exp (-h * t) * FI t
  have hq0 : IntegrableOn q (Ioi (0 : ℝ)) := weightedFI_integrable hh
  have hq1 : IntegrableOn q (Ioi (1 : ℝ)) :=
    hq0.mono_set (Ioi_subset_Ioi (by norm_num))
  have hq2 : IntegrableOn q (Ioi (2 : ℝ)) :=
    hq1.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit01 := intervalIntegral.integral_interval_add_Ioi hq0 hq1
  have hsplit12 := intervalIntegral.integral_interval_add_Ioi hq1 hq2
  have hzero : (∫ t in (0 : ℝ)..1, q t) = 0 := by
    have hcongr : (∫ t in (0 : ℝ)..1, q t) =
        ∫ _t in (0 : ℝ)..1, (0 : ℝ) :=
      intervalIntegral.integral_congr (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      change Real.exp (-h * t) * FI t = 0
      rw [FI_of_le_one ht'.2, mul_zero])
    exact hcongr.trans intervalIntegral.integral_zero
  change (∫ t in Ioi (0 : ℝ), q t) = _
  calc
    (∫ t in Ioi (0 : ℝ), q t) =
        (∫ t in (0 : ℝ)..1, q t) + ∫ t in Ioi (1 : ℝ), q t := hsplit01.symm
    _ = ∫ t in Ioi (1 : ℝ), q t := by rw [hzero, zero_add]
    _ = (∫ t in (1 : ℝ)..2, q t) + ∫ t in Ioi (2 : ℝ), q t := hsplit12.symm
    _ = (Real.exp (-h) / h ^ 2 - Real.exp (-2 * h) / h -
          Real.exp (-2 * h) / h ^ 2) + Real.exp (-2 * h) / h := by
      rw [weightedFI_middle_integral hh, weightedFI_tail_integral hh]
    _ = (Real.exp (-h) - Real.exp (-2 * h)) / h ^ 2 := by ring

/-- IMP-R13: the exact interval indicator has the clipped primitive, which is
bounded, eventually constant, and nondifferentiable at both corners. For every
positive weight, both T06 hypotheses and both exact weighted values hold.
@isnad1 id=and.0h0v.s9.57c8beb6fa58 from=translated src=- shape=6b5ba025 vocab=15ba1d6a
-/
theorem indicatorPrimitive_nondifferentiable :
    IsFiniteExceptionalPrimitive gI 0 ∅ FI ∧
      ¬ DifferentiableAt ℝ FI 1 ∧ ¬ DifferentiableAt ℝ FI 2 ∧
      (∀ t : ℝ, 0 ≤ FI t ∧ FI t ≤ 1) ∧
      (∀ t : ℝ, 2 ≤ t → FI t = 1) ∧
      (∀ h : ℝ, 0 < h →
        IntegrableOn (fun t : ℝ => Real.exp (-h * t) * FI t) (Ioi 0) ∧
        Tendsto (fun R : ℝ => Real.exp (-h * R) * FI R) atTop (nhds 0) ∧
        IntegrableOn (fun t : ℝ => Real.exp (-h * t) * gI t) (Ioi 0) ∧
        (∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FI t) =
          (Real.exp (-h) - Real.exp (-2 * h)) / h ^ 2 ∧
        (∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * gI t) =
          (Real.exp (-h) - Real.exp (-2 * h)) / h ∧
        HasImproperIntegralAtTopExcept
          (fun t : ℝ => Real.exp (-h * t) * gI t) 0 ∅
          ((Real.exp (-h) - Real.exp (-2 * h)) / h)) := by
  refine ⟨indicatorPrimitive, FI_not_differentiableAt_one,
    FI_not_differentiableAt_two, fun t => ⟨FI_nonneg t, FI_le_one t⟩,
    fun t ht => FI_of_two_le ht, ?_⟩
  intro h hh
  refine ⟨weightedFI_integrable hh, weightedFI_tendsto hh,
    weightedgI_integrable hh, weightedFI_integral hh, weightedgI_integral hh, ?_⟩
  have hrel := indicatorPrimitive.hasImproperIntegralAtTopExcept_exp_smul h
    (by simpa [smul_eq_mul] using weightedFI_integrable hh)
    (by simpa [smul_eq_mul] using weightedFI_tendsto hh)
  have hrel' : HasImproperIntegralAtTopExcept
      (fun t : ℝ => Real.exp (-h * t) * gI t) 0 ∅
      (h * ∫ t in Ioi (0 : ℝ), Real.exp (-h * t) * FI t) := by
    simpa [smul_eq_mul] using hrel
  rw [weightedFI_integral hh] at hrel'
  have hvalue :
      h * ((Real.exp (-h) - Real.exp (-2 * h)) / h ^ 2) =
        (Real.exp (-h) - Real.exp (-2 * h)) / h := by
    field_simp [ne_of_gt hh]
  rw [hvalue] at hrel'
  exact hrel'

end LMLFTest.Integral.Improper
