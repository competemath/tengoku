import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Regression.Projection
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Regression.Spheres

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
lemma run_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) (n : ℕ) :
    L.run s ω x n = L.run t ω x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    split
    · rfl
    · split
      · rw [h]
      · rfl

lemma estimate_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) : L.estimate s ω x = L.estimate t ω x := by
  simp only [estimate, terminal, run_congr_labels L s t ω x h]

lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

def localNormalize (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) (r : ℝ) : Measure E :=
  (C * ENNReal.ofReal (r^a))⁻¹ • (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

omit [FiniteDimensional ℝ E] in
lemma localNormalize_univ {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    localNormalize ν a C z r univ ≤ 1 := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  simp only [localNormalize, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z))) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (mul_le_mul' le_rfl (hν z r hr)).trans_eq (ENNReal.inv_mul_cancel hc0 hct)

omit [FiniteDimensional ℝ E] in
lemma localNormalize_finite {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (localNormalize ν a C z r) :=
  ⟨(localNormalize_univ hν hC hCt z hr).trans_lt (by simp)⟩

omit [FiniteDimensional ℝ E] in
lemma localNormalize_support (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (localNormalize ν a C z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, localNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : E => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩ Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_local {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    HasLocalMassBound (localNormalize ν a C z r) (a : ℝ) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  intro t _ ρ hρ
  rw [localNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : E => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x - (z+r • t) = r • (r⁻¹ • (x-z) - t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * ν (Metric.closedBall (z+r • t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * (C * ENNReal.ofReal ((r*ρ)^a)) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (ρ^(a : ℝ)) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le a), ← mul_assoc C,
        ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, Real.rpow_natCast]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma replicaConstant_le {ν : Measure E} (hν : ν univ ≤ 1) {a m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E) :
    replicaConstant ν (a : ℝ) m ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have h2 : (2 : ℝ≥0∞) ≤ 2^d := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hd
  have hp : (2 : ℝ≥0∞)^(m+1) ≤ 4^d := by
    rw [pow_succ]
    calc
      _ ≤ (2 : ℝ≥0∞)^d * 2^d := mul_le_mul' (pow_le_pow_right₀ (by norm_num) hm) h2
      _ = _ := by rw [← mul_pow]; norm_num
  calc
    replicaConstant ν (a : ℝ) m ≤ 1 + (4 : ℝ≥0∞)^d * 4^d * 4^d := by
      unfold replicaConstant
      rw [Real.rpow_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr <;> norm_num
    _ = 1 + (64 : ℝ≥0∞)^d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (2 : ℝ≥0∞) * 64^d := by
      rw [two_mul]
      exact add_le_add (one_le_pow₀ (by norm_num)) le_rfl
    _ ≤ (2 : ℝ≥0∞)^d * 64^d := mul_le_mul' h2 le_rfl
    _ = _ := by rw [← mul_pow]; norm_num; rfl

lemma finite_rpow_holder {J : Type*} [Fintype J] (a : J → ℝ≥0∞) {q : ℝ} (hq : 1 < q) :
    (∑ j, a j ^ (1 - 1/q)) ≤
      (Fintype.card J : ℝ≥0∞)^(1/q) * (∑ j, a j)^(1-1/q) := by
  have hh := Real.HolderConjugate.conjExponent hq
  have hq' : q.conjExponent ≠ 0 := ne_of_gt hh.symm.pos
  have hex : 1 - 1/q = q.conjExponent⁻¹ := by simpa only [one_div] using hh.one_sub_inv
  rw [hex]
  simpa only [one_mul, one_div, ENNReal.one_rpow, ENNReal.rpow_inv_rpow hq',
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun _ : J => (1 : ℝ≥0∞))
      (fun j => a j ^ q.conjExponent⁻¹) hh

lemma projectionLaw_affine (ν : Measure E) [SFinite ν] (m : ℕ) (z : E) (r : ℝ) :
    projectionLaw (ν.map (fun t => z + r • t)) m =
      (projectionLaw ν m).map (fun x => (x.1, fun j => ⟪z,x.1 j⟫ + r * x.2 j)) := by
  unfold projectionLaw
  rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => stdGaussian E)),
    Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_id, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x <;> simp [inner_add_left, real_inner_smul_left]

lemma projectionLaw_withDensity_apply (μ : Measure E) [SFinite μ] {h : E → ℝ≥0∞}
    (hh : Measurable h) [SFinite (μ.withDensity h)] (m : ℕ)
    {S : Set ((Fin m → E) × (Fin m → ℝ))} (hS : MeasurableSet S) :
    projectionLaw (μ.withDensity h) m S =
      ∫⁻ s, h s * (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (A, fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian E)) ∂μ := by
  have hobs : Measurable (fun x : (Fin m → E) × E => (x.1, fun j => ⟪x.2,x.1 j⟫)) := by fun_prop
  have hi : Measurable (fun x : (Fin m → E) × E => S.indicator (fun _ => (1 : ℝ≥0∞))
      (x.1, fun j => ⟪x.2,x.1 j⟫)) :=
    ((measurable_const : Measurable (fun _ => (1 : ℝ≥0∞))).indicator hS).comp hobs
  rw [projectionLaw, Measure.map_apply hobs hS]
  rw [← one_mul (((Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) _),
    ← lintegral_indicator_const (hobs hS) 1]
  change (∫⁻ x : (Fin m → E) × E, S.indicator (fun _ => (1 : ℝ≥0∞))
    (x.1, fun j => ⟪x.2,x.1 j⟫) ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) = _
  rw [lintegral_prod_symm _ hi.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul μ hh hi.lintegral_prod_left]
  rfl

def blockValue {J : Type*} [Fintype J] {m : ℕ} (h : J → E → ℝ≥0∞)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) : ℝ≥0∞ :=
  ∫⁻ A, h (φ (A, fun j => ⟪s,A j⟫)) s ∂Measure.pi (fun _ : Fin m => stdGaussian E)

lemma measurable_finite_select {X J : Type*} [MeasurableSpace X] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {h : J → X → ℝ≥0∞} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) := by
  classical
  have he (x : X) : h (φ x) x = ∑ j : J, if φ x = j then h j x else 0 := by simp
  simp_rw [he]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_eq_fun hφ measurable_const) (hh j) measurable_const

lemma measurable_blockValue {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {m : ℕ} {h : J → E → ℝ≥0∞}
    (hh : ∀ j, Measurable (h j)) {φ : ((Fin m → E) × (Fin m → ℝ)) → J}
    (hφ : Measurable φ) : Measurable (blockValue h φ) := by
  apply Measurable.lintegral_prod_left
  exact measurable_finite_select (fun j => (hh j).comp measurable_snd)
    (hφ.comp (by fun_prop))

lemma blockValue_mass_identity (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {m : ℕ} {h : J → E → ℝ≥0∞} (hh : ∀ j, Measurable (h j))
    (hh1 : ∀ j s, h j s ≤ 1)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ)
    {S : Set E} (hS : MeasurableSet S) :
    (μ.withDensity (blockValue h φ)) S =
      ∑ j, projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} := by
  classical
  let g (j : J) (s : E) (A : Fin m → E) : ℝ≥0∞ :=
    if φ (A, fun k => ⟪s,A k⟫) = j then h j s else 0
  have hg (j : J) : Measurable (Function.uncurry (g j)) := by
    exact Measurable.ite (measurableSet_eq_fun (hφ.comp (by fun_prop)) measurable_const)
      ((hh j).comp measurable_fst) measurable_const
  have hselect (s : E) (A : Fin m → E) : h (φ (A, fun k => ⟪s,A k⟫)) s = ∑ j, g j s A := by
    simp [g]
  have he (j : J) : projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} =
      ∫⁻ s in S, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
    rw [restrict_withDensity hS]
    let : IsFiniteMeasure ((μ.restrict S).withDensity (h j)) :=
      isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
    rw [projectionLaw_withDensity_apply _ (hh j) _ (measurableSet_eq_fun hφ measurable_const)]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 j s).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    by_cases hx : φ (A, fun k => ⟪s,A k⟫) = j <;> simp [g, hx]
  rw [withDensity_apply _ hS]
  calc
    _ = ∫⁻ s in S, ∑ j, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
      apply lintegral_congr
      intro s
      unfold blockValue
      simp_rw [hselect]
      exact lintegral_finsetSum _ (fun j _ => (hg j).comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_finsetSum _ (fun j _ => (hg j).lintegral_prod_right)]
      simp_rw [he]

end SubsphereRegression

end

end OAI
