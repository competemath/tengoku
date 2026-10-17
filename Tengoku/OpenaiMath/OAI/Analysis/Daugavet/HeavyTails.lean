import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.SignAverages

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe u_1 uIota

namespace ExactModuli.KW

section HeavySums
variable {ι : Type uIota} [Fintype ι]

def coefficientNorm (p : ℝ) (a : ι → ℝ) : ℝ := (∑ j, |a j| ^ p) ^ (1 / p)

/--
@isnad1 id=le.0h3v.s4.c3632065d292 from=translated src=- shape=f5081c45 vocab=e6361464
-/
lemma coefficientNorm_nonneg (p : ℝ) (a : ι → ℝ) : 0 ≤ coefficientNorm p a :=
  Real.rpow_nonneg (Finset.sum_nonneg
    (fun index _ => Real.rpow_nonneg (abs_nonneg (a index)) _)) _

/--
@isnad1 id=eq.1h3v.s5.3e1bf3fb4116 from=translated src=- shape=707bdd60 vocab=164b45bd
-/
lemma coefficientNorm_rpow {p : ℝ} (hp : 0 < p) (a : ι → ℝ) :
    coefficientNorm p a ^ p = ∑ j, |a j| ^ p := by
  unfold coefficientNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _))]
  have he : (1 / p) * p = 1 := by field_simp
  rw [he, Real.rpow_one]

/--
@isnad1 id=le.1h4v.s5.3fa0c3afd414 from=translated src=- shape=b7e067c3 vocab=c0be7f18
-/
lemma abs_le_coefficientNorm {p : ℝ} (hp : 0 < p) (a : ι → ℝ) (j : ι) :
    |a j| ≤ coefficientNorm p a := by
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) (coefficientNorm_nonneg p a) hp).mp
  rw [coefficientNorm_rpow hp a]
  exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (abs_nonneg _) p) (Finset.mem_univ j)

/--
@isnad1 id=eq.2h4v.s6.d837b2b31d0f from=translated src=- shape=1afda8fd vocab=dc9aa556
-/
lemma sum_scaled_coefficients {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) (a : ι → ℝ) :
    ∑ j, (s * |a j|) ^ p = (s * coefficientNorm p a) ^ p := by
  rw [Real.mul_rpow hs (coefficientNorm_nonneg p a), coefficientNorm_rpow hp a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact Real.mul_rpow hs (abs_nonneg _)

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.1h5v.s7.13a0ffa432c0 from=translated src=- shape=3e023398 vocab=1e6e1c05
-/
lemma difference_law_tail [IsProbabilityMeasure μ] {Y : Ω → ℝ} {p u : ℝ}
    (hY : IdentDistrib Y (difference p) μ pairedMeasure) :
    μ.real {ω | u < |Y ω|} = pairedMeasure.real {v | u < |difference p v|} := by
  exact congrArg ENNReal.toReal (hY.measure_mem_eq
    (measurableSet_lt measurable_const measurable_abs))

/--
@isnad1 id=le.3h6v.s7.2be29d812afe from=translated src=- shape=9705e4cb vocab=edb2511d
-/
lemma scaled_difference_tail_upper {Y : Ω → ℝ} {p u : ℝ}
    (hp : 1 < p) (hY : IdentDistrib Y (difference p) μ pairedMeasure)
    (a : ℝ) (hu : 0 < u) :
    μ.real {ω | u < |a * Y ω|} ≤ 2 * (scale p * |a|) ^ p * u ^ (-p) := by
  by_cases ha : a = 0
  · subst a
    simp [hu.not_gt, Real.zero_rpow (by linarith : p ≠ 0)]
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have hevent : {ω | u < |a * Y ω|} = {ω | u / |a| < |Y ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [abs_mul, div_lt_iff₀ ha0, mul_comm |a|]
  rw [hevent, difference_law_tail hY]
  refine (difference_tail_upper hp (div_pos hu ha0)).trans_eq ?_
  have hdiv : scale p / (u / |a|) = (scale p * |a|) / u := by field_simp
  rw [hdiv, Real.div_rpow (by positivity [scale_pos hp]) hu.le, Real.rpow_neg hu.le]
  ring

/--
@isnad1 id=le.5h6v.s7.98da69a3a2cd from=translated src=- shape=de98d655 vocab=61f9bd56
-/
lemma scaled_difference_tail_lower {Y : Ω → ℝ} {p u : ℝ}
    (hp : 1 < p) (hpmax : p ≤ 3 / 2) (hY : IdentDistrib Y (difference p) μ pairedMeasure)
    (a : ℝ) (hu : 0 < u) (husa : scale p * |a| ≤ u) :
    (1 / 18) * (scale p * |a|) ^ p * u ^ (-p) ≤ μ.real {ω | u < |a * Y ω|} := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have hevent : {ω | u < |a * Y ω|} = {ω | u / |a| < |Y ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [abs_mul, div_lt_iff₀ ha0, mul_comm |a|]
  rw [hevent, difference_law_tail hY]
  have hlow := difference_tail_lower hp hpmax ((le_div_iff₀ ha0).mpr husa)
  have hdiv : scale p / (u / |a|) = (scale p * |a|) / u := by field_simp
  rw [hdiv, Real.div_rpow (by positivity [scale_pos hp]) hu.le] at hlow
  rw [Real.rpow_neg hu.le]
  convert hlow using 1
  ring

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=identdis.1h5v.s6.1cdf5213955e from=translated src=- shape=0b25c7a0 vocab=178a0b29
-/
lemma scaled_difference_symmetric [IsProbabilityMeasure μ] {Y : Ω → ℝ} {p : ℝ}
    (hY : IdentDistrib Y (difference p) μ pairedMeasure) (a : ℝ) :
    IdentDistrib (fun ω => a * Y ω) (fun ω => -(a * Y ω)) μ μ := by
  have hs := (hY.trans (difference_symmetric p)).trans hY.neg.symm
  have ha := hs.const_mul a
  simpa only [Pi.neg_apply, mul_neg] using ha

/--
@isnad1 id=le.6h7v.s7.e182f5e21937 from=translated src=- shape=9f90b0ad vocab=eb027678
-/
theorem heavy_tail_upper (Y : ι → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hlaw : ∀ j, IdentDistrib (Y j) (difference p) μ pairedMeasure)
    (a : ι → ℝ) {u : ℝ} (hu : 0 < u) :
    μ.real {ω | u < |∑ j, a j * Y j ω|} ≤
      10 * (scale p * coefficientNorm p a / u) ^ p := by
  have hs := scale_pos hp
  have hp0 : 0 < p := by linarith
  have hp2 : p < 2 := by linarith
  have hind' := hind.comp (fun j x => a j * x) (fun j => measurable_const.mul measurable_id)
  have hb := independent_symmetric_sum_tail (fun j ω => a j * Y j ω)
    (fun j => (hY j).const_mul _) hind' (fun j => scaled_difference_symmetric (hlaw j) (a j))
    hp0 hp2 (fun j => 2 * (scale p * |a j|) ^ p) (fun j => by positivity)
    (fun j t ht => scaled_difference_tail_upper hp (hlaw j) (a j) ht) hu
  rw [← Finset.mul_sum, sum_scaled_coefficients hp0 hs.le a] at hb
  have hconst : 2 / (2 - p) ≤ 4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hconst' : (1 + 2 / (2 - p)) * 2 ≤ 10 := by linarith
  have hm := mul_le_mul_of_nonneg_right hconst'
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg hs.le (coefficientNorm_nonneg p a)) p)
      (Real.rpow_nonneg hu.le (-p)))
  rw [Real.div_rpow (mul_nonneg hs.le (coefficientNorm_nonneg p a)) hu.le]
  rw [Real.rpow_neg hu.le] at hm hb
  simp only [div_eq_mul_inv] at *
  nlinarith

end HeavySums

end ExactModuli.KW

end

end OAI
