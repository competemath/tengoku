import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Entropy

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

def actualExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d × W) × Rows m d)) :
    Measure (((Sphere d × W) × Rows m d) × Rows r d) := P.prod (gaussianRows r d)

instance actualExperiment_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (actualExperiment (r:=r) P) :=
  inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))

def actualRowsSignal {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) : Rows (m+r) d × Sphere d :=
  (Fin.append p.1.2 p.2,p.1.1.1)

def actualObservation {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) :
    (Rows (m+r) d × W) × (Fin (m+r) → ℝ) :=
  ((Fin.append p.1.2 p.2,p.1.1.2), label (Fin.append p.1.2 p.2) (p.1.1.1 : Vector d))

def selectedCube {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d)) (δ : ℝ)
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := cubeAverage (ρ z.1.2) z.1.1 z.2 δ

def selectedExact {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d))
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := exactDensity (ρ z.1.2) z.1.1 z.2

lemma measurable_countable_selection {A B T W : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace T] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (f : W → A×B → T)
    (hf : ∀ w, Measurable (f w)) :
    Measurable (fun z : (A×W)×B => f z.1.2 (z.1.1,z.2)) := by
  have hh : Measurable (fun z : (A×B)×W => f z.2 z.1) :=
    measurable_from_prod_countable_left hf
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_selectedCube {k d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (ρ : W → Measure (Sphere d))
    [∀ w, SFinite (ρ w)] (δ : ℝ) : Measurable (selectedCube (k:=k) ρ δ) :=
  measurable_countable_selection (fun w gy => cubeAverage (ρ w) gy.1 gy.2 δ)
    (fun w => measurable_cubeAverage (ρ w) δ)

lemma measurable_selectedExact {k d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (ρ : W → Measure (Sphere d))
    [∀ w, SFinite (ρ w)] : Measurable (selectedExact (k:=k) ρ) :=
  measurable_countable_selection (fun w gy => exactDensity (ρ w) gy.1 gy.2)
    (fun w => measurable_exactDensity (ρ w))

lemma exactDensity_ne_top {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d) (y : Fin k → ℝ) :
    exactDensity ρ G y ≠ ∞ := by
  unfold exactDensity
  dsimp only
  split_ifs <;> simp

def momentBound (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ :=
  Real.exp (C*d)*B*(1+max (Real.log (D/B)) 0)

lemma momentBound_nonneg (C : ℝ) (d : ℕ) {B D : ℝ} (hB : 0 ≤ B) :
    0 ≤ momentBound C d B D := by
  unfold momentBound
  positivity

lemma cubeAverage_inner_finite {d m r : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (s : Sphere d) (X : Rows m d) (δ : ℝ) :
    ∫⁻ Z, cubeAverage ρ (Fin.append X Z) (label (Fin.append X Z) (s:Vector d)) δ
      ∂gaussianRows r d ≠ ∞ := by
  apply ne_top_of_le_ne_top (b:=ENNReal.ofReal ((2*δ)⁻¹^(m+r))*ρ univ)
  · finiteness
  · calc
      _ ≤ ∫⁻ _Z : Rows r d, ENNReal.ofReal ((2*δ)⁻¹^(m+r))*ρ univ ∂gaussianRows r d := by
        apply lintegral_mono; intro Z
        exact mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
      _ = _ := by simp

lemma log_lintegral_bound_of_ae_tendsto {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : ℕ → A → ℝ≥0∞) (F : A → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hFt : ∀ a, F a ≠ ∞)
    (ht : ∀ᵐ a ∂μ, Tendsto (fun j => f j a) atTop (𝓝 (F a)))
    (R : ℝ≥0∞) (hR : ∀ j ≥ 1, ∫⁻ a, ENNReal.ofReal (Real.log (1+(f j a).toReal)) ∂μ ≤ R) :
    ∫⁻ a, ENNReal.ofReal (Real.log (1+(F a).toReal)) ∂μ ≤ R := by
  let g : ℕ → A → ℝ≥0∞ := fun j a => ENNReal.ofReal (Real.log (1+(f j a).toReal))
  have hlim : ∀ᵐ a ∂μ, liminf (fun j => g j a) atTop = ENNReal.ofReal (Real.log (1+(F a).toReal)) := by
    filter_upwards [ht] with a ha
    have htr := (ENNReal.continuousAt_toReal (hFt a)).tendsto.comp ha
    have hlog := (tendsto_const_nhds.add htr).log (show 1+(F a).toReal ≠ 0 by positivity)
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hlog).liminf_eq
  calc
    _ = ∫⁻ a, liminf (fun j => g j a) atTop ∂μ := lintegral_congr_ae (hlim.mono fun a ha => ha.symm)
    _ ≤ liminf (fun j => ∫⁻ a, g j a ∂μ) atTop :=
      lintegral_liminf_le (fun j => (measurable_log_one_add (hf j)).ennreal_ofReal)
    _ ≤ R := liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      ((eventually_ge_atTop 1).mono fun j hj => hR j hj).frequently

def logPositive (x : ℝ≥0∞) : ℝ := max (Real.log x.toReal) 0

def logNegative (x : ℝ≥0∞) : ℝ≥0∞ := if x = 0 then ∞ else ENNReal.ofReal (-Real.log x.toReal)

def extendedLogExpectation {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) : EReal :=
  ((∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ) : EReal) -
    ((∫⁻ a, logNegative (f a) ∂μ) : EReal)

lemma logPositive_le_log_one_add (x : ℝ≥0∞) : logPositive x ≤ Real.log (1+x.toReal) := by
  apply max_le _ (log_one_add_nonneg x)
  by_cases h : x.toReal = 0
  · simp only [h, Real.log_zero, add_zero, Real.log_one, le_refl]
  · exact Real.log_le_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)) (le_add_of_nonneg_left zero_le_one)

lemma log_bound_consequences {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) (hf : Measurable f) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∫⁻ a, ENNReal.ofReal (Real.log (1+(f a).toReal)) ∂μ ≤ ENNReal.ofReal R) :
    (Integrable (fun a => Real.log (1+(f a).toReal)) μ ∧
      ∫ a, Real.log (1+(f a).toReal) ∂μ ≤ R) ∧
    Integrable (fun a => logPositive (f a)) μ ∧ extendedLogExpectation μ f ≤ (R:EReal) := by
  have hLi : Integrable (fun a => Real.log (1+(f a).toReal)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_log_one_add hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hR)
  have hLf : ∫ a, Real.log (1+(f a).toReal) ∂μ ≤ R := by
    rw [← ofReal_integral_eq_lintegral_ofReal hLi
      (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)] at hR
    exact (ENNReal.ofReal_le_ofReal_iff hR0).mp hR
  have hPi : Integrable (fun a => logPositive (f a)) μ := by
    apply hLi.mono' ((hf.ennreal_toReal.log.max measurable_const).aestronglyMeasurable)
    apply Filter.Eventually.of_forall; intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact logPositive_le_log_one_add _
  refine ⟨⟨hLi,hLf⟩,hPi,?_⟩
  have hPL : ∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ ≤ ENNReal.ofReal R :=
    (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (logPositive_le_log_one_add _)).trans hR
  apply (EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hPL)
    (EReal.coe_ennreal_nonneg (∫⁻ a, logNegative (f a) ∂μ))).trans
  have he : (ENNReal.ofReal R : EReal) = (R:EReal) :=
    by simpa using (EReal.coe_toENNReal (x := (R:EReal)) (by exact_mod_cast hR0))
  simp only [sub_zero, he, le_refl]

def PositiveMessage {W : Type*} [MeasurableSpace W] (π : Measure W) := {w : W // 0 < π {w}}

def completeFamily {W : Type*} [MeasurableSpace W] {T : Type*} (π : Measure W)
    (f : PositiveMessage π → T) (t₀ : T) (w : W) : T :=
  if h : 0 < π {w} then f ⟨w,h⟩ else t₀

lemma completeFamily_pos {W : Type*} [MeasurableSpace W] (π : Measure W)
    (f : PositiveMessage π → ℝ) (hf : ∀ w, 0 < f w) (w : W) :
    0 < completeFamily π f 1 w := by
  unfold completeFamily
  split_ifs with h
  · exact hf ⟨w,h⟩
  · norm_num

lemma completeFamily_growth {W : Type*} [MeasurableSpace W] {d a : ℕ}
    (π : Measure W) (ρ : PositiveMessage π → Measure (Sphere d))
    (B : PositiveMessage π → ℝ) (hg : ∀ w, LocalGrowth (ρ w) a (B w)) (w : W) :
    LocalGrowth (completeFamily π ρ 0 w) a (completeFamily π B 1 w) := by
  unfold completeFamily
  split_ifs with h
  · exact hg ⟨w,h⟩
  · intro z t ht
    simp

structure ActualRowConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : rowInformation P (gaussianRows m d) ≠ ∞
  row_le_entropy : (rowInformation P (gaussianRows m d)).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)

theorem actualRowRefinement {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e)
    (_hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) (gaussianRows m d) =
      rowInformation P (gaussianRows m d) :=
  rowInformation_refinement P (gaussianRows m d) e he

end CurrentProjection

end

end OAI
