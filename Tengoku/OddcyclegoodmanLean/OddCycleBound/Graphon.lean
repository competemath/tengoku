import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

structure IsGraphon (U : Ω → Ω → ℝ) (μ : Measure Ω) : Prop where
  meas : Measurable (Function.uncurry U)
  nonneg : ∀ x y, 0 ≤ U x y
  le_one : ∀ x y, U x y ≤ 1
  symm : ∀ x y, U x y = U y x

private lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans (le_of_eq (by rw [abs_neg]))

structure Good (f : Ω → ℝ) : Prop where
  meas : StronglyMeasurable f
  bdd : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C

/--
@isnad1 id=integrab.1h3v.s5.5e9cdffd992a from=translated src=- shape=4c60f492 vocab=2e50cd3a
-/
lemma Good.integrable {f : Ω → ℝ} (hf : Good f) : Integrable f μ := by
  obtain ⟨C, _, hC⟩ := hf.bdd
  refine (integrable_const C).mono' hf.meas.aestronglyMeasurable (ae_of_all _ ?_)
  intro x; simpa [Real.norm_eq_abs] using hC x

/--
@isnad1 id=good.2h3v.s5.abf40893c529 from=translated src=- shape=e7bce992 vocab=302af2fb
-/
lemma Good.mul {f k : Ω → ℝ} (hf : Good f) (hk : Good k) : Good (fun x => f x * k x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Ck, hCk0, hCk⟩ := hk.bdd
  refine ⟨hf.meas.mul hk.meas, ⟨Cf * Ck, mul_nonneg hCf0 hCk0, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hCf x) (hCk x) (abs_nonneg _) hCf0

variable {U : Ω → Ω → ℝ}

noncomputable def kernelOp (U : Ω → Ω → ℝ) (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => ∫ y, U x y * f y ∂μ

noncomputable def mean (μ : Measure Ω) (f : Ω → ℝ) : ℝ := ∫ x, f x ∂μ

/--
@isnad1 id=eq.0h3v.s4.92bb8e686bbd from=translated src=- shape=15764bb3 vocab=03b73225
-/
lemma mean_const (c : ℝ) : mean μ (fun _ => c) = c := by simp [mean]

/--
@isnad1 id=good.2h4v.s5.25290d06c6d8 from=translated src=- shape=c77b720d vocab=03fc6e17
-/
lemma good_kernelOp (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) : Good (kernelOp U μ f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨?_, ⟨C, hC0, fun x => ?_⟩⟩
  · have hSM : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2 * f p.2) :=
      (hU.meas.stronglyMeasurable).mul (hf.meas.comp_measurable measurable_snd)
    exact hSM.integral_prod_right'
  · have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
    have hint : Integrable (fun y => U x y * f y) μ :=
      (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
        rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable
    calc |kernelOp U μ f x| ≤ ∫ y, |U x y * f y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _y, C ∂μ := by
          refine integral_mono hint.abs (integrable_const C) (fun y => ?_)
          rw [abs_mul, abs_of_nonneg (hU.nonneg x y)]
          calc U x y * |f y| ≤ 1 * |f y| :=
                mul_le_mul_of_nonneg_right (hU.le_one x y) (abs_nonneg _)
            _ = |f y| := one_mul _
            _ ≤ C := hC y
      _ = C := by simp

noncomputable def degree (U : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → ℝ := fun x => ∫ y, U x y ∂μ

noncomputable def edgeDensity (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℝ := mean μ (degree U μ)

noncomputable def degCentered (U : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → ℝ :=
  fun x => degree U μ x - edgeDensity U μ

noncomputable def compress (U : Ω → Ω → ℝ) (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => kernelOp U μ f x - mean μ (kernelOp U μ f)

noncomputable def compressIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => degCentered U μ
  | (n + 1) => compress U μ (compressIter U μ n)

noncomputable def specMoment (U : Ω → Ω → ℝ) (μ : Measure Ω) (j : ℕ) : ℝ :=
  ∫ x, degCentered U μ x * compressIter U μ j x ∂μ

/--
@isnad1 id=good.1h3v.s5.6f696c17f249 from=translated src=- shape=8883064b vocab=9d84bc80
-/
lemma good_degree (hU : IsGraphon U μ) : Good (degree U μ) := by
  have h : degree U μ = kernelOp U μ (fun _ => 1) := by funext x; simp [degree, kernelOp]
  rw [h]; exact good_kernelOp hU ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

/--
@isnad1 id=good.1h3v.s5.13b4f7dd4acd from=translated src=- shape=8883064b vocab=6dacef55
-/
lemma good_degCentered (hU : IsGraphon U μ) : Good (degCentered U μ) := by
  obtain ⟨C, hC0, hC⟩ := (good_degree hU).bdd
  refine ⟨(good_degree hU).meas.sub stronglyMeasurable_const,
    ⟨C + |edgeDensity U μ|, add_nonneg hC0 (abs_nonneg _), fun x => ?_⟩⟩
  exact (abs_sub_le' _ _).trans (by linarith [hC x])

/--
@isnad1 id=good.2h4v.s5.a43738f59e0b from=translated src=- shape=c77b720d vocab=678adf98
-/
lemma good_compress (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) : Good (compress U μ f) := by
  obtain ⟨C, hC0, hC⟩ := (good_kernelOp hU hf).bdd
  refine ⟨(good_kernelOp hU hf).meas.sub stronglyMeasurable_const,
    ⟨C + |mean μ (kernelOp U μ f)|, add_nonneg hC0 (abs_nonneg _), fun x => ?_⟩⟩
  exact (abs_sub_le' _ _).trans (by linarith [hC x])

/--
@isnad1 id=good.1h4v.s5.38a4f417150d from=translated src=- shape=c680d783 vocab=13ad3174
-/
lemma good_compressIter (hU : IsGraphon U μ) : ∀ k, Good (compressIter U μ k)
  | 0 => good_degCentered hU
  | (k + 1) => good_compress hU (good_compressIter hU k)

/--
@isnad1 id=eq.1h4v.s5.71544b992f43 from=translated src=- shape=b00e313d vocab=6606f48d
-/
lemma mean_compressIter (hU : IsGraphon U μ) : ∀ k, mean μ (compressIter U μ k) = 0
  | 0 => by
      show ∫ x, degCentered U μ x ∂μ = 0
      simp only [degCentered]
      rw [integral_sub (good_degree hU).integrable (integrable_const _)]
      show mean μ (degree U μ) - mean μ (fun _ => edgeDensity U μ) = 0
      rw [mean_const, edgeDensity]; ring
  | (k + 1) => by
      show ∫ x, compress U μ (compressIter U μ k) x ∂μ = 0
      simp only [compress]
      rw [integral_sub (good_kernelOp hU (good_compressIter hU k)).integrable (integrable_const _)]
      show mean μ (kernelOp U μ (compressIter U μ k)) - mean μ (fun _ => mean μ (kernelOp U μ (compressIter U μ k))) = 0
      rw [mean_const]; ring

/--
@isnad1 id=eq.3h5v.s6.319bd536bed1 from=translated src=- shape=cbbd279c vocab=dc508665
-/
lemma kernelOp_symm (hU : IsGraphon U μ) {f k : Ω → ℝ} (hf : Good f) (hk : Good k) :
    ∫ x, kernelOp U μ f x * k x ∂μ = ∫ x, f x * kernelOp U μ k x ∂μ := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Ck, hCk0, hCk⟩ := hk.bdd
  have hSM : StronglyMeasurable (Function.uncurry fun x y => U x y * f y * k x) := by
    have h1 : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2) := hU.meas.stronglyMeasurable
    have h2 : StronglyMeasurable (fun p : Ω × Ω => f p.2) := hf.meas.comp_measurable measurable_snd
    have h3 : StronglyMeasurable (fun p : Ω × Ω => k p.1) := hk.meas.comp_measurable measurable_fst
    exact (h1.mul h2).mul h3
  have hInt : Integrable (Function.uncurry fun x y => U x y * f y * k x) (μ.prod μ) := by
    refine (integrable_const (1 * Cf * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (hU.nonneg x y)]
    refine mul_le_mul (mul_le_mul (hU.le_one x y) (hCf y) (abs_nonneg _) (by norm_num)) (hCk x)
      (abs_nonneg _) (mul_nonneg zero_le_one hCf0)
  have hL : ∀ x, kernelOp U μ f x * k x = ∫ y, U x y * f y * k x ∂μ := fun x => by
    rw [kernelOp, integral_mul_const]
  have hR : ∀ y, f y * kernelOp U μ k y = ∫ x, U x y * f y * k x ∂μ := fun y => by
    rw [kernelOp, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show f y * (U y x * k x) = U x y * f y * k x
    rw [hU.symm y x]; ring
  calc ∫ x, kernelOp U μ f x * k x ∂μ
      = ∫ x, ∫ y, U x y * f y * k x ∂μ ∂μ := by simp_rw [hL]
    _ = ∫ y, ∫ x, U x y * f y * k x ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ y, f y * kernelOp U μ k y ∂μ := by simp_rw [hR]

/--
@isnad1 id=eq.5h5v.s7.e1a0dd386d09 from=translated src=- shape=412e0f25 vocab=8841343f
-/
lemma compress_symm (hU : IsGraphon U μ) {f k : Ω → ℝ} (hf : Good f) (hk : Good k)
    (hf0 : mean μ f = 0) (hk0 : mean μ k = 0) :
    ∫ x, compress U μ f x * k x ∂μ = ∫ x, f x * compress U μ k x ∂μ := by
  have e1 : ∫ x, compress U μ f x * k x ∂μ = ∫ x, kernelOp U μ f x * k x ∂μ := by
    have h1 : Integrable (fun x => kernelOp U μ f x * k x) μ := ((good_kernelOp hU hf).mul hk).integrable
    have h2 : Integrable (fun x => mean μ (kernelOp U μ f) * k x) μ := hk.integrable.const_mul _
    calc ∫ x, compress U μ f x * k x ∂μ
        = ∫ x, (kernelOp U μ f x * k x - mean μ (kernelOp U μ f) * k x) ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_); simp only [compress]; ring
      _ = (∫ x, kernelOp U μ f x * k x ∂μ) - mean μ (kernelOp U μ f) * ∫ x, k x ∂μ := by
            rw [integral_sub h1 h2, integral_const_mul]
      _ = ∫ x, kernelOp U μ f x * k x ∂μ := by
            have hk0' : ∫ x, k x ∂μ = 0 := hk0
            rw [hk0']; ring
  have e2 : ∫ x, f x * compress U μ k x ∂μ = ∫ x, f x * kernelOp U μ k x ∂μ := by
    have h1 : Integrable (fun x => f x * kernelOp U μ k x) μ := (hf.mul (good_kernelOp hU hk)).integrable
    have h2 : Integrable (fun x => f x * mean μ (kernelOp U μ k)) μ := hf.integrable.mul_const _
    calc ∫ x, f x * compress U μ k x ∂μ
        = ∫ x, (f x * kernelOp U μ k x - f x * mean μ (kernelOp U μ k)) ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_); simp only [compress]; ring
      _ = (∫ x, f x * kernelOp U μ k x ∂μ) - (∫ x, f x ∂μ) * mean μ (kernelOp U μ k) := by
            rw [integral_sub h1 h2, integral_mul_const]
      _ = ∫ x, f x * kernelOp U μ k x ∂μ := by
            have hf0' : ∫ x, f x ∂μ = 0 := hf0
            rw [hf0']; ring
  rw [e1, e2, kernelOp_symm hU hf hk]

/--
@isnad1 id=eq.1h5v.s6.166533a060a5 from=translated src=- shape=9f60ab5a vocab=c68c68e6
-/
lemma moment (hU : IsGraphon U μ) : ∀ (j i : ℕ),
    ∫ x, compressIter U μ i x * compressIter U μ j x ∂μ = specMoment U μ (i + j) := by
  intro j
  induction j with
  | zero =>
      intro i
      rw [Nat.add_zero]
      show ∫ x, compressIter U μ i x * degCentered U μ x ∂μ = ∫ x, degCentered U μ x * compressIter U μ i x ∂μ
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      ring
  | succ n ih =>
      intro i
      have key : ∫ x, compressIter U μ i x * compressIter U μ (n + 1) x ∂μ
          = ∫ x, compressIter U μ (i + 1) x * compressIter U μ n x ∂μ := by
        show ∫ x, compressIter U μ i x * compress U μ (compressIter U μ n) x ∂μ
            = ∫ x, compress U μ (compressIter U μ i) x * compressIter U μ n x ∂μ
        exact (compress_symm hU (good_compressIter hU i) (good_compressIter hU n) (mean_compressIter hU i) (mean_compressIter hU n)).symm
      rw [key, ih (i + 1)]
      congr 1; omega

end OddCycleBound
