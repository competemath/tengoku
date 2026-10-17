import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.SliceCharacterization

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

def scale (p : ℝ) : ℝ := (p - 1) / p

def multiplier (p : ℝ) (v : unitInterval) : ℝ := scale p * (v : ℝ) ^ (-1 / p)

/--
@isnad1 id=lt.1h1v.s4.f41252eae1b6 from=translated src=- shape=35bd48ee vocab=050487a1
-/
lemma scale_pos {p : ℝ} (hp : 1 < p) : 0 < scale p := by
  dsimp [scale]; positivity

/--
@isnad1 id=lt.1h1v.s4.a6aaf73105b5 from=translated src=- shape=3965f485 vocab=050487a1
-/
lemma scale_lt_one {p : ℝ} (hp : 1 < p) : scale p < 1 := by
  unfold scale
  rw [div_lt_one (by linarith : 0 < p)]
  linarith

/--
@isnad1 id=le.1h2v.s4.d22e2fa55df7 from=translated src=- shape=ffc2f2eb vocab=5976b76f
-/
lemma multiplier_nonneg {p : ℝ} (hp : 1 < p) (v : unitInterval) :
    0 ≤ multiplier p v := mul_nonneg (scale_pos hp).le (Real.rpow_nonneg v.property.1 _)

/--
@isnad1 id=measurab.0h1v.s4.750bcee94b34 from=translated src=- shape=5352fdf6 vocab=251e2794
-/
lemma measurable_multiplier (p : ℝ) : Measurable (multiplier p) := by
  unfold multiplier
  fun_prop

/--
@isnad1 id=integrab.1h1v.s5.8d16f1a1f951 from=translated src=- shape=7c15cb4d vocab=a75c9e2a
-/
lemma integrable_multiplier {p : ℝ} (hp : 1 < p) :
    Integrable (multiplier p) (volume : Measure unitInterval) := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 < -1 / p := by rw [lt_div_iff₀ hp0]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (-1 / p)) (Icc 0 1) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
      ((intervalIntegral.intervalIntegrable_rpow' hexp).1)
  have hc := (unitInterval.measurePreserving_coe.integrable_comp hi.aestronglyMeasurable).mpr hi
  exact hc.const_mul (scale p)

/--
@isnad1 id=eq.1h1v.s5.3aae3c4f6522 from=translated src=- shape=293c0be0 vocab=03f83b88
-/
lemma integral_multiplier {p : ℝ} (hp : 1 < p) :
    ∫ v : unitInterval, multiplier p v = 1 := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 < -1 / p := by rw [lt_div_iff₀ hp0]; linarith
  unfold multiplier
  rw [integral_const_mul]
  change scale p * (∫ x : Icc (0:ℝ) 1, (x:ℝ) ^ (-1 / p)) = 1
  rw [integral_subtype measurableSet_Icc (fun x : ℝ => x ^ (-1 / p)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_rpow (Or.inl hexp)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : -1 / p + 1 ≠ 0)]
  dsimp [scale]
  field_simp [hp0.ne', show p - 1 ≠ 0 by linarith, show -1 + p ≠ 0 by linarith]
  ring

/--
@isnad1 id=eq.2h2v.s6.c9ac438cd502 from=translated src=- shape=cf29b90f vocab=02cb9682
-/
lemma multiplier_tail {p u : ℝ} (hp : 1 < p) (hu : scale p ≤ u) :
    (volume : Measure unitInterval).real {v | u < multiplier p v} = (scale p / u) ^ p := by
  have hs : 0 < scale p := scale_pos hp
  have hu0 : 0 < u := hs.trans_le hu
  have hp0 : 0 < p := by linarith
  let q := (scale p / u) ^ p
  have hq : 0 < q := Real.rpow_pos_of_pos (div_pos hs hu0) _
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact Real.rpow_le_one (by positivity) ((div_le_one hu0).mpr hu) hp0.le
  let a : unitInterval := ⟨q, hq.le, hq1⟩
  have hqpow : q ^ (-1 / p) = u / scale p := by
    dsimp [q]
    rw [← Real.rpow_mul (div_pos hs hu0).le]
    have hm : p * (-1 / p) = -1 := by field_simp
    rw [hm, Real.rpow_neg_one, inv_div]
  have haeq : {v : unitInterval | u < multiplier p v} =ᵐ[volume] Iio a := by
    have hne : ∀ᵐ v : unitInterval, v ≠ 0 := volume.ae_ne 0
    filter_upwards [hne] with v hv
    have hv0 : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (by
      intro heq; apply hv; apply Subtype.ext; exact heq.symm)
    apply propext
    change (u < scale p * (v : ℝ) ^ (-1 / p)) ↔ (v : ℝ) < q
    have hueq : u = scale p * q ^ (-1 / p) := by rw [hqpow]; field_simp
    rw [hueq, mul_lt_mul_iff_right₀ hs,
      Real.rpow_lt_rpow_iff_of_neg hq hv0 (div_neg_of_neg_of_pos (by norm_num) hp0)]
  rw [measureReal_congr haeq, measureReal_def, unitInterval.volume_Iio,
    ENNReal.toReal_ofReal hq.le]

/--
@isnad1 id=le.2h2v.s6.4cd15d19b1ce from=translated src=- shape=5d1aab91 vocab=02cb9682
-/
lemma multiplier_tail_le {p u : ℝ} (hp : 1 < p) (hu : 0 < u) :
    (volume : Measure unitInterval).real {v | u < multiplier p v} ≤ (scale p / u) ^ p := by
  by_cases hs : scale p ≤ u
  · exact le_of_eq (multiplier_tail hp hs)
  · have hsu : 1 ≤ (scale p / u) ^ p := Real.one_le_rpow
      ((le_div_iff₀ hu).mpr (by linarith : 1 * u ≤ scale p)) (by linarith)
    exact (measureReal_le_one).trans hsu

abbrev pairedMeasure : Measure (unitInterval × unitInterval) :=
  (volume : Measure unitInterval).prod volume

def difference (p : ℝ) (v : unitInterval × unitInterval) : ℝ :=
  multiplier p v.1 - multiplier p v.2

/--
@isnad1 id=measurab.0h1v.s5.eaed439a97bf from=translated src=- shape=fca95677 vocab=df4996ec
-/
lemma measurable_difference (p : ℝ) : Measurable (difference p) :=
  ((measurable_multiplier p).comp measurable_fst).sub
    ((measurable_multiplier p).comp measurable_snd)

/--
@isnad1 id=integrab.1h1v.s6.97100674325c from=translated src=- shape=815187b1 vocab=1da22e61
-/
lemma integrable_difference {p : ℝ} (hp : 1 < p) :
    Integrable (difference p) pairedMeasure := by
  exact ((measurePreserving_fst.integrable_comp
    (integrable_multiplier hp).aestronglyMeasurable).mpr (integrable_multiplier hp)).sub
    ((measurePreserving_snd.integrable_comp
    (integrable_multiplier hp).aestronglyMeasurable).mpr (integrable_multiplier hp))

/--
@isnad1 id=identdis.0h1v.s6.f8bdf5de0c11 from=translated src=- shape=4ad552f5 vocab=b964f9bf
-/
lemma difference_symmetric (p : ℝ) :
    IdentDistrib (difference p) (fun v => -difference p v) pairedMeasure pairedMeasure := by
  have hcomp : (fun v => -difference p v) = difference p ∘ Prod.swap := by
    funext v
    simp [difference, sub_eq_add_neg, add_comm]
  refine ⟨(measurable_difference p).aemeasurable,
    (measurable_difference p).neg.aemeasurable, ?_⟩
  rw [hcomp, ← Measure.map_map (measurable_difference p) measurable_swap, Measure.prod_swap]

/--
@isnad1 id=le.2h2v.s7.4d8f0387ed77 from=translated src=- shape=68955b8d vocab=e4555ff5
-/
lemma difference_tail_upper {p u : ℝ} (hp : 1 < p) (hu : 0 < u) :
    pairedMeasure.real {v | u < |difference p v|} ≤ 2 * (scale p / u) ^ p := by
  let A := {v : unitInterval | u < multiplier p v}
  have hsub : {v | u < |difference p v|} ⊆ (A ×ˢ univ) ∪ (univ ×ˢ A) := by
    intro v hv
    change u < |multiplier p v.1 - multiplier p v.2| at hv
    by_contra hn
    have he : multiplier p v.1 ≤ u ∧ multiplier p v.2 ≤ u := by
      simpa [A] using hn
    have h1 := multiplier_nonneg hp v.1
    have h2 := multiplier_nonneg hp v.2
    have hb : |multiplier p v.1 - multiplier p v.2| ≤ u :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  calc
    _ ≤ pairedMeasure.real ((A ×ˢ univ) ∪ (univ ×ˢ A)) := measureReal_mono hsub
    _ ≤ pairedMeasure.real (A ×ˢ univ) + pairedMeasure.real (univ ×ˢ A) := measureReal_union_le _ _
    _ = 2 * (volume : Measure unitInterval).real A := by
      rw [measureReal_prod_prod, measureReal_prod_prod]
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (multiplier_tail_le hp hu) (by norm_num)

/--
@isnad1 id=le.3h2v.s7.8c91614ef682 from=translated src=- shape=ef6fdb49 vocab=e4555ff5
-/
lemma difference_tail_lower {p u : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hu : scale p ≤ u) :
    (1 / 18) * (scale p / u) ^ p ≤ pairedMeasure.real {v | u < |difference p v|} := by
  have hs : 0 < scale p := scale_pos hp
  have hu0 : 0 < u := hs.trans_le hu
  have hp0 : 0 < p := by linarith
  let B := {v : unitInterval | u + 2 * scale p < multiplier p v}
  let C := {v : unitInterval | 2 * scale p < multiplier p v}ᶜ
  have hsub : B ×ˢ C ⊆ {v | u < |difference p v|} := by
    intro v hv
    have hB : u + 2 * scale p < multiplier p v.1 := hv.1
    have hC : multiplier p v.2 ≤ 2 * scale p := le_of_not_gt hv.2
    have hdiff : u < difference p v := by dsimp [difference]; linarith
    exact hdiff.trans_le (le_abs_self _)
  have hB : (volume : Measure unitInterval).real B = (scale p / (u + 2 * scale p)) ^ p :=
    multiplier_tail hp (by linarith)
  have hC : (1 / 2 : ℝ) ≤ (volume : Measure unitInterval).real C := by
    have heq : scale p / (2 * scale p) = (1 / 2 : ℝ) := by field_simp
    have hpow : (1 / 2 : ℝ) ^ p ≤ 1 / 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hp.le
    have hvol : (volume : Measure unitInterval).real univ = 1 := by simp
    dsimp [C]
    rw [measureReal_compl (measurableSet_lt measurable_const (measurable_multiplier p)),
      hvol, multiplier_tail hp (by linarith), heq]
    linarith
  have hB9 : (scale p / u) ^ p ≤ 9 * (volume : Measure unitInterval).real B := by
    rw [hB]
    have hd : (scale p / u) / 3 ≤ scale p / (u + 2 * scale p) := by
      rw [div_div]
      apply (div_le_div_iff₀ (by positivity : 0 < u * 3) (by positivity)).mpr
      nlinarith
    have hpow := Real.rpow_le_rpow (show 0 ≤ (scale p / u) / 3 by positivity) hd hp0.le
    rw [Real.div_rpow (by positivity) (by norm_num)] at hpow
    have h3 : (3:ℝ) ^ p ≤ 9 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
        (show p ≤ 2 by linarith)
      norm_num at h
      exact h
    have hin := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) p)).mp hpow
    have hmul := mul_le_mul_of_nonneg_right h3
      (Real.rpow_nonneg (by positivity : 0 ≤ scale p / (u + 2 * scale p)) p)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hC
    (measureReal_nonneg : 0 ≤ (volume : Measure unitInterval).real B)
  have hm := measureReal_mono (μ := pairedMeasure) hsub
  rw [measureReal_prod_prod] at hm
  nlinarith

end ExactModuli.KW

end

end OAI
