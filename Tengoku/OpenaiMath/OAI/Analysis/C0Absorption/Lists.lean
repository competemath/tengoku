import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Signs

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def completedSigma (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  (squareWeight n)⁻¹ • completedCoordinate L o n

/--
@isnad1 id=eq.0h5v.s10.14f35ceac8a9 from=translated src=- shape=7a86113e vocab=069278c2
-/
@[simp] theorem completedSigma_coe (n : ℕ) (m : PreSpace L o) :
    completedSigma L o n (toTestSpace L o m) =
      sigma (L (triple n).1) (listConstant n) (listExponent n) m := by
  simp only [completedSigma, smul_apply, NNReal.smul_def, NNReal.coe_inv,
    completedCoordinate_coe, smul_eq_mul]
  change (squareWeight n : ℝ)⁻¹ * ((squareWeight n : ℝ) *
    sigma (L (triple n).1) (listConstant n) (listExponent n) m) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul]

/--
@isnad1 id=continuo.0h4v.s8.16f1b7e808ca from=translated src=- shape=b0310bac vocab=109ca155
-/
theorem completedSigma_continuous (n : ℕ) : Continuous (completedSigma L o n) :=
  continuous_const.mul (completedCoordinate_continuous L o n)

/--
@isnad1 id=le.0h5v.s9.5d30bf63e0ce from=translated src=- shape=d65b8b62 vocab=67c81fce
-/
theorem sigma_le_preNorm (n : ℕ) (m : PreSpace L o) :
    sigma (L (triple n).1) (listConstant n) (listExponent n) m ≤
      (squareWeight n : ℝ)⁻¹ * ‖m‖ := by
  have h := selectedCoordinate_le_norm L o n m
  change (squareWeight n : ℝ) *
    sigma (L (triple n).1) (listConstant n) (listExponent n) m ≤ 1 * ‖m‖ at h
  rw [one_mul] at h
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (squareWeight n).coe_nonneg)
  simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul] using hm

/--
@isnad1 id=le.0h5v.s8.d754dc64c0bb from=translated src=- shape=15343ed9 vocab=591376a7
-/
theorem completedSigma_le (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (completedSigma_continuous L o n) (by fun_prop)
  | ih m =>
    change completedSigma L o n (toTestSpace L o m) ≤
      (squareWeight n : ℝ)⁻¹ * ‖toTestSpace L o m‖
    rw [completedSigma_coe, norm_toTestSpace]
    exact sigma_le_preNorm L o n m

def initialList (n : ℕ) (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    PreSpace L o →L[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) :=
  (show PreSpace L o →ₗ[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) from
    l.eval (listExponent n)).mkContinuous (squareWeight n : ℝ)⁻¹ (fun m => by
      exact (list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

def completedList (n : ℕ) (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    TestSpace L o →L[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) :=
  (initialList L o n l).extend (toTestSpace L o)

/--
@isnad1 id=eq.0h6v.s11.5fc1fc4d1c89 from=translated src=- shape=a459d1e9 vocab=56728d0e
-/
@[simp] theorem completedList_coe (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (m : PreSpace L o) :
    completedList L o n l (toTestSpace L o m) = l.eval (listExponent n) m :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (PreSpace L o)) m

/--
@isnad1 id=le.0h6v.s10.e7d90c0b0e0e from=translated src=- shape=1675b4a9 vocab=b7142a3e
-/
theorem completedList_le_sigma (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) :
    ‖completedList L o n l z‖ ≤ completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_le (completedList L o n l).continuous.norm
      (completedSigma_continuous L o n)
  | ih m =>
    change ‖completedList L o n l (toTestSpace L o m)‖ ≤
      completedSigma L o n (toTestSpace L o m)
    rw [completedList_coe, completedSigma_coe]
    exact list_le_sigma _ _ _ o l m

def completedListNorm (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) : Seminorm ℝ (TestSpace L o) :=
  (normSeminorm ℝ _).comp (completedList L o n l).toLinearMap

/--
@isnad1 id=bddabove.0h4v.s10.4b2b54a15c56 from=translated src=- shape=1f4b15bd vocab=200e246e
-/
theorem completedListNorm_bddAbove (n : ℕ) :
    BddAbove (Set.range (completedListNorm L o n)) := by
  refine ⟨completedSigma L o n, ?_⟩
  rintro _ ⟨l, rfl⟩ z
  exact completedList_le_sigma L o n l z

def sigmaFromLists (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  ⨆ l, completedListNorm L o n l

/--
@isnad1 id=le.0h5v.s8.c46ca50e8233 from=translated src=- shape=15343ed9 vocab=ba919294
-/
theorem sigmaFromLists_le (n : ℕ) (z : TestSpace L o) :
    sigmaFromLists L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  rw [sigmaFromLists, Seminorm.iSup_apply (completedListNorm_bddAbove L o n)]
  exact ciSup_le fun l => (completedList_le_sigma L o n l z).trans
    (completedSigma_le L o n z)

/--
@isnad1 id=eq.0h5v.s9.93024665111f from=translated src=- shape=fcbdcc04 vocab=26935391
-/
theorem sigmaFromLists_eq (n : ℕ) (z : TestSpace L o) :
    sigmaFromLists L o n z = completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq (seminorm_lipschitz (sigmaFromLists L o n) ((squareWeight n)⁻¹)
      (sigmaFromLists_le L o n)).continuous (completedSigma_continuous L o n)
  | ih m =>
    change sigmaFromLists L o n (toTestSpace L o m) =
      completedSigma L o n (toTestSpace L o m)
    rw [sigmaFromLists, Seminorm.iSup_apply (completedListNorm_bddAbove L o n),
      completedSigma_coe]
    refine Eq.trans ?_ (sigma_apply _ _ _ o (show Molecule S from m)).symm
    apply congrArg iSup
    funext l
    exact congrArg norm (completedList_coe L o n l m)

/--
@isnad1 id=eq.0h5v.s10.fa846ddbd60d from=translated src=- shape=d92153ad vocab=1ef95982
-/
theorem completedSigma_eq_iSup (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z =
      ⨆ l : AdmissibleList (L (triple n).1) (listConstant n), ‖completedList L o n l z‖ := by
  rw [← sigmaFromLists_eq, sigmaFromLists,
    Seminorm.iSup_apply (completedListNorm_bddAbove L o n)]
  rfl

end CompletedLists

section InterpolationAndDenseLimits

 /--
 @isnad1 id=eq.1h3v.s6.e43534e5ec11 from=translated src=- shape=d77fa4c3 vocab=c79c8ada
 -/
 theorem finite_lp_norm_rpow {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (x : PiLp p (fun _ : ι => ℝ)) :
    ‖x‖ ^ p.toReal = ∑ i, |x i| ^ p.toReal := by
  rw [PiLp.norm_eq_sum hp, ← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

 /--
 @isnad1 id=le.4h5v.s7.bc0476fde7f6 from=translated src=- shape=f19f8699 vocab=b5705c3c
 -/
 theorem finite_lp_interpolation {ι : Type*} [Fintype ι]
    (p q : ℝ≥0∞) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (hqp : q.toReal < p.toReal) (x : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, |x i| ≤ δ) :
    ‖WithLp.toLp p x‖ ^ p.toReal ≤
      δ ^ (p.toReal - q.toReal) * ‖WithLp.toLp q x‖ ^ q.toReal := by
  rw [finite_lp_norm_rpow p hp, finite_lp_norm_rpow q hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change |x i| ^ p.toReal ≤ δ ^ (p.toReal - q.toReal) * |x i| ^ q.toReal
  calc
    |x i| ^ p.toReal = |x i| ^ (p.toReal - q.toReal) * |x i| ^ q.toReal := by
      rw [← Real.rpow_add' (abs_nonneg _) (by simpa using hp.ne'), sub_add_cancel]
    _ ≤ δ ^ (p.toReal - q.toReal) * |x i| ^ q.toReal := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (abs_nonneg _) (hδ i) (sub_nonneg.mpr hqp.le))
        (Real.rpow_nonneg (abs_nonneg _) _)

/--
@isnad1 id=ex.5h4v.s7.c3f6163aab18 from=translated src=- shape=e06a4adf vocab=02761052
-/
theorem exists_uniform_lp_detector (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hqp : q.toReal < p.toReal)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin n → ℝ),
      a ≤ ‖WithLp.toLp p x‖ → ‖WithLp.toLp q x‖ ≤ B →
      ∃ i, δ < |x i| := by
  let A := a ^ p.toReal
  let D := B ^ q.toReal
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hD : 0 < D := Real.rpow_pos_of_pos hB _
  have hs : 0 < p.toReal - q.toReal := sub_pos.mpr hqp
  let δ := (A / (2 * D)) ^ (1 / (p.toReal - q.toReal))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hA (mul_pos (by norm_num) hD)) _
  have hpow : δ ^ (p.toReal - q.toReal) = A / (2 * D) := by
    rw [show δ = (A / (2 * D)) ^ (1 / (p.toReal - q.toReal)) from rfl,
      ← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  refine ⟨δ, hδ, ?_⟩
  intro n x hlow hupp
  by_contra! hnone
  have hint := finite_lp_interpolation p q hp hq hqp x δ hnone
  have hlu : A ≤ ‖WithLp.toLp p x‖ ^ p.toReal := Real.rpow_le_rpow ha.le hlow hp.le
  have huu : ‖WithLp.toLp q x‖ ^ q.toReal ≤ D :=
    Real.rpow_le_rpow (norm_nonneg _) hupp hq.le
  have hb := mul_le_mul_of_nonneg_left huu (Real.rpow_nonneg hδ.le (p.toReal - q.toReal))
  rw [hpow] at hint hb
  have heq : A / (2 * D) * D = A / 2 := by field_simp [ne_of_gt hD]
  rw [heq] at hb
  linarith

/--
@isnad1 id=tendsto.4h8v.s6.9cfaec2b7262 from=translated src=- shape=f00c1a01 vocab=34b723d3
-/
theorem tendsto_of_dense_lipschitz {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : A → X) (hd : DenseRange d) (f : ℕ → X → Y) (g : X → Y) (K : ℝ≥0)
    (hf : ∀ n, LipschitzWith K (f n)) (hg : LipschitzWith K g)
    (h : ∀ a, Filter.Tendsto (fun n => f n (d a)) Filter.atTop (nhds (g (d a))))
    (x : X) : Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hK : 0 < 3 * ((K : ℝ) + 1) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x (div_pos hε hK)
  have hδ : (K : ℝ) * dist x (d a) < ε / 3 := by
    have hr := (lt_div_iff₀ hK).mp ha
    have hn := dist_nonneg (x := x) (y := d a)
    nlinarith
  filter_upwards [Metric.tendsto_nhds.mp (h a) (ε / 3) (by positivity)] with n hn
  have h₁ := (hf n).dist_le_mul x (d a)
  have h₂ := hg.dist_le_mul (d a) x
  rw [dist_comm (d a) x] at h₂
  have ht := dist_triangle4 (f n x) (f n (d a)) (g (d a)) (g x)
  linarith

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI
