/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Native three-dimensional coordinate vectors. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Three-dimensional coordinate vectors equipped with their Euclidean L² norm. -/
abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)

/-- Space-time points, given the parabolic metric below rather than the product metric. -/
def ParabolicPoint := Vec3 × ℝ

/--
@isnad1 id=lt.0h0v.s5.c5efbe6b1e27 from=translated src=- shape=5ee22617 vocab=b02f647b
-/
theorem half_pos : 0 < (1 / 2 : ℝ) := by norm_num

/--
@isnad1 id=le.0h0v.s5.2d3c72780838 from=translated src=- shape=7f6a8e6b vocab=951fdf53
-/
theorem half_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num

/-- Time equipped with the square-root snowflake metric. -/
abbrev SnowTime := Metric.Snowflaking ℝ (1 / 2 : ℝ) half_pos half_le_one

/-- Euclidean length of a native three-dimensional coordinate vector. -/
def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))

instance : MeasurableSpace SnowTime := borel SnowTime

instance : BorelSpace SnowTime := ⟨rfl⟩

/-- Measurable equivalence to Euclidean space times snowflaked time. -/
def parabolicMeasurableEquiv : ParabolicPoint ≃ᵐ L2Vec3 × SnowTime :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 Vec3) {
    toEquiv := Metric.Snowflaking.toSnowflaking
    measurable_toFun := Metric.Snowflaking.continuous_toSnowflaking.measurable
    measurable_invFun := Metric.Snowflaking.homeomorph.continuous.measurable }

/-- Coordinate map into the product carrying the parabolic metric. -/
def parabolicMap (p : ParabolicPoint) :
    L2Vec3 × SnowTime := parabolicMeasurableEquiv p

/--
@isnad1 id=injectiv.0h0v.s2.926a21274fc6 from=translated src=- shape=583fb3b9 vocab=43ce50e2
-/
lemma parabolicMap_injective : Function.Injective parabolicMap := by
  intro p q h
  exact parabolicMeasurableEquiv.injective h

noncomputable instance parabolicMetricSpace : MetricSpace ParabolicPoint :=
  MetricSpace.induced parabolicMap parabolicMap_injective inferInstance

/-- Pseudometric presentation of the parabolic metric for explicit metric-space arguments. -/
abbrev parabolicPseudoMetricSpace : PseudoMetricSpace ParabolicPoint :=
  MetricSpace.toPseudoMetricSpace (self := parabolicMetricSpace)

instance : BorelSpace ParabolicPoint :=
  MeasurableEmbedding.borelSpace parabolicMeasurableEquiv.measurableEmbedding
    (Topology.IsInducing.induced parabolicMap)

/--
@isnad1 id=eq.0h1v.s6.76bf29ae6824 from=translated src=- shape=220fd7d4 vocab=2cb7b1e6
-/
lemma vec3EuclideanNorm_eq_l2 (v : Vec3) :
    vec3EuclideanNorm v = ‖WithLp.toLp 2 v‖ := by
  rw [vec3EuclideanNorm, PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sq_abs]

/--
@isnad1 id=le.0h1v.s3.5bf8f8931707 from=translated src=- shape=b9369acb vocab=a3f20d52
-/
lemma vec3EuclideanNorm_nonneg (v : Vec3) : 0 ≤ vec3EuclideanNorm v := by
  exact Real.sqrt_nonneg _

/--
@isnad1 id=eq.0h0v.s5.e005f7be7474 from=translated src=- shape=1ac31801 vocab=3f56e89c
-/
lemma vec3EuclideanNorm_zero : vec3EuclideanNorm (0 : Vec3) = 0 := by
  simp [vec3EuclideanNorm]

/--
@isnad1 id=eq.0h2v.s5.57be138c05ef from=translated src=- shape=81171e50 vocab=ed9a875e
-/
lemma vec3EuclideanNorm_smul (a : ℝ) (v : Vec3) :
    vec3EuclideanNorm (a • v) = |a| * vec3EuclideanNorm v := by
  rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    ← vec3EuclideanNorm_eq_l2]

/-- Maximum of spatial Euclidean distance and square-root time separation. -/
def parabolicDist (p q : ParabolicPoint) : ℝ :=
  max (vec3EuclideanNorm (p.1 - q.1)) (Real.sqrt |p.2 - q.2|)

/--
@isnad1 id=eq.0h2v.s4.e14162eab9d2 from=translated src=- shape=4974a109 vocab=4e0d65c3
-/
lemma dist_eq_parabolicDist (p q : ParabolicPoint) :
    dist p q = parabolicDist p q := by
  simp only [parabolicDist, vec3EuclideanNorm_eq_l2, Real.sqrt_eq_rpow]
  rfl

/-- Open Euclidean ball in native spatial coordinates. -/
def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}

/-- Backward parabolic cylinder with spatial radius `r` and time depth `r ^ 2`. -/
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t

/--
@isnad1 id=iff.0h3v.s5.236d7864a0a8 from=translated src=- shape=c3555f3b vocab=914bff83
-/
@[simp] lemma mem_vec3Ball {x y : Vec3} {r : ℝ} :
    y ∈ vec3Ball x r ↔ vec3EuclideanNorm (y - x) < r := Iff.rfl

/--
@isnad1 id=iff.0h5v.s6.31e2f2244c6f from=translated src=- shape=185d2bcc vocab=87ec462b
-/
@[simp] lemma mem_parabolicCylinder {x y : Vec3} {t s r : ℝ} :
    (y, s) ∈ parabolicCylinder x t r ↔
      vec3EuclideanNorm (y - x) < r ∧ t - r ^ 2 < s ∧ s ≤ t := by
  rfl

/--
@isnad1 id=le.1h3v.s4.0bec9a92e168 from=translated src=- shape=9a6dd29f vocab=f0354dd4
-/
lemma vec3Ball_mono {x : Vec3} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    vec3Ball x r₁ ⊆ vec3Ball x r₂ := by
  intro y hy
  exact hy.trans_le hr

/--
@isnad1 id=le.2h4v.s5.e768144397c5 from=translated src=- shape=affe701e vocab=d9727960
-/
lemma parabolicCylinder_mono {x : Vec3} {t r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂) :
    parabolicCylinder x t r₁ ⊆ parabolicCylinder x t r₂ := by
  intro p hp
  rcases hp with ⟨hp₁, hp₂, hp₃⟩
  refine ⟨vec3Ball_mono hr hp₁, ?_, hp₃⟩
  have hr₂ : 0 ≤ r₂ := hr₁.trans hr
  have hrsq : r₁ ^ 2 ≤ r₂ ^ 2 := (sq_le_sq₀ hr₁ hr₂).2 hr
  exact (sub_le_sub_left hrsq t).trans_lt hp₂

/-- Space-time translation by a spatial vector and time offset. -/
def parabolicTranslate (a : Vec3) (τ : ℝ) (p : ParabolicPoint) : ParabolicPoint :=
  (a + p.1, τ + p.2)

/-- Parabolic scaling, linear in space and quadratic in time. -/
def parabolicScale (a : ℝ) (p : ParabolicPoint) : ParabolicPoint :=
  (a • p.1, a ^ 2 * p.2)

/--
@isnad1 id=eq.0h5v.s6.2d3a5cf510db from=translated src=- shape=ed7c1d35 vocab=a912aceb
-/
lemma parabolicCylinder_translate (a x : Vec3) (τ t r : ℝ) :
    parabolicTranslate a τ '' parabolicCylinder x t r =
      parabolicCylinder (a + x) (τ + t) r := by
  ext p
  constructor
  · rintro ⟨⟨z, u⟩, hz, rfl⟩
    rcases hz with ⟨hz₁, hz₂, hz₃⟩
    change vec3EuclideanNorm ((a + z) - (a + x)) < r ∧
      τ + t - r ^ 2 < τ + u ∧ τ + u ≤ τ + t
    refine ⟨?_, ?_, ?_⟩
    · have hdiff : (a + z) - (a + x) = z - x := by abel
      rw [hdiff]
      exact hz₁
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz₂
    · simpa [add_assoc, add_left_comm, add_comm] using hz₃
  · intro hp
    rcases p with ⟨y, s⟩
    rcases hp with ⟨hp₁, hp₂, hp₃⟩
    refine ⟨(y - a, s - τ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [vec3Ball, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₁
      · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₂
      · simpa [add_assoc, add_left_comm, add_comm] using hp₃
    · apply Prod.ext <;> simp [parabolicTranslate, sub_eq_add_neg]

/--
@isnad1 id=eq.1h4v.s6.f07ef614f92e from=translated src=- shape=5a335c5e vocab=1a57fb85
-/
lemma parabolicCylinder_scale {x : Vec3} {t r a : ℝ} (ha : 0 < a) :
    parabolicScale a '' parabolicCylinder x t r =
      parabolicCylinder (a • x) (a ^ 2 * t) (a * r) := by
  ext p
  rcases p with ⟨y, s⟩
  constructor
  · rintro ⟨⟨z, u⟩, hz, hzy⟩
    change (a • z, a ^ 2 * u) = (y, s) at hzy
    have hy : y = a • z := by
      exact (congrArg Prod.fst hzy).symm
    have hs : s = a ^ 2 * u := by
      exact (congrArg Prod.snd hzy).symm
    rw [hy, hs]
    rcases hz with ⟨hz₁, hz₂, hz₃⟩
    change vec3EuclideanNorm (a • z - a • x) < a * r ∧
      a ^ 2 * t - (a * r) ^ 2 < a ^ 2 * u ∧ a ^ 2 * u ≤ a ^ 2 * t
    refine ⟨?_, ?_, ?_⟩
    · rw [← smul_sub, vec3EuclideanNorm_smul, abs_of_pos ha]
      exact mul_lt_mul_of_pos_left hz₁ ha
    · have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      have h := mul_lt_mul_of_pos_left hz₂ ha2
      calc
        a ^ 2 * t - (a * r) ^ 2 = a ^ 2 * (t - r ^ 2) := by ring
        _ < a ^ 2 * u := h
    · exact mul_le_mul_of_nonneg_left hz₃ (le_of_lt (sq_pos_of_pos ha))
  · intro hp
    rcases hp with ⟨hp₁, hp₂, hp₃⟩
    refine ⟨(a⁻¹ • y, a⁻¹ ^ 2 * s), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · change vec3EuclideanNorm (a⁻¹ • y - x) < r
        have hdiff : a⁻¹ • y - x = a⁻¹ • (y - a • x) := by
          rw [smul_sub, smul_smul]
          simp [ha.ne']
        rw [hdiff, vec3EuclideanNorm_smul, abs_inv, abs_of_pos ha]
        have h := mul_lt_mul_of_pos_left hp₁ (inv_pos.mpr ha)
        simpa [ha.ne'] using h
      · have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
        have hmul : a ^ 2 * (t - r ^ 2) < a ^ 2 * (a⁻¹ ^ 2 * s) := by
          calc
            a ^ 2 * (t - r ^ 2) = a ^ 2 * t - (a * r) ^ 2 := by ring
            _ < s := hp₂
            _ = a ^ 2 * (a⁻¹ ^ 2 * s) := by field_simp [ha.ne']
        have h := lt_of_mul_lt_mul_left hmul (le_of_lt ha2)
        exact h
      · apply le_of_mul_le_mul_left _ (sq_pos_of_pos ha)
        simpa [ha.ne'] using hp₃
    · apply Prod.ext
      · simp [parabolicScale, smul_smul, ha.ne']
      · change a ^ 2 * (a⁻¹ ^ 2 * s) = s
        field_simp [ha.ne']

instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))

/--
@isnad1 id=measurab.0h2v.s5.f9fcad598c73 from=translated src=- shape=1ed02776 vocab=61a9dceb
-/
lemma vec3Ball_measurable (x : Vec3) (r : ℝ) : MeasurableSet (vec3Ball x r) := by
  have hmeas : Measurable (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact hmeas measurableSet_Iio

/--
@isnad1 id=eq.0h2v.s7.da7047ca5e79 from=translated src=- shape=7e148c2b vocab=ff668a36
-/
lemma volume_vec3Ball (x : Vec3) (r : ℝ) :
    volume (vec3Ball x r) = volume (vec3Ball 0 r) := by
  have hpre : (fun y : Vec3 => x + y) ⁻¹' vec3Ball x r = vec3Ball 0 r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, sub_zero]
    abel_nf
  have h := (measurePreserving_add_left (volume : Measure Vec3) x).measure_preimage
    (vec3Ball_measurable x r).nullMeasurableSet
  rw [hpre] at h
  exact h.symm

/--
@isnad1 id=eq.0h3v.s7.c7aaf627c594 from=translated src=- shape=e2f11ad6 vocab=993664f5
-/
lemma volume_parabolicCylinder (x : Vec3) (t r : ℝ) :
    volume (parabolicCylinder x t r) =
      volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2) := by
  rw [parabolicCylinder]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t) =
    volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2)
  rw [Measure.prod_prod]
  rw [Real.volume_Ioc]
  congr 2
  ring

/--
@isnad1 id=eq.0h3v.s7.78a50e113bdc from=translated src=- shape=b135937d vocab=993664f5
-/
lemma volume_parabolicCylinder_zero (x : Vec3) (t r : ℝ) :
    volume (parabolicCylinder x t r) =
      volume (vec3Ball 0 r) * ENNReal.ofReal (r ^ 2) := by
  rw [volume_parabolicCylinder, volume_vec3Ball]

/-- Hausdorff measure computed using the parabolic metric and the real value of the exponent. -/
def parabolicHausdorffMeasure (d : ℝ≥0∞) : Measure ParabolicPoint :=
  MeasureTheory.Measure.hausdorffMeasure d.toReal

end CKN.Foundation.Parabolic
