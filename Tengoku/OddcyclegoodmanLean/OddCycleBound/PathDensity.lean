import Tengoku.OddcyclegoodmanLean.OddCycleBound.Graphon

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

lemma good_one : Good (fun _ : Ω => (1 : ℝ)) :=
  ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

lemma good_smul (c : ℝ) {f : Ω → ℝ} (hf : Good f) : Good (c • f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.const_smul c, ⟨|c| * C, mul_nonneg (abs_nonneg _) hC0, fun x => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma good_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f + g) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨hf.meas.add hg.meas, ⟨Cf + Cg, by linarith, fun x => ?_⟩⟩
  rw [Pi.add_apply]
  exact (abs_add_le _ _).trans (by linarith [hCf x, hCg x])

lemma integrable_Uf (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    Integrable (fun y => U x y * f y) μ := by
  have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
  exact (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable

omit [IsProbabilityMeasure μ] in
lemma kernelOp_one (_hU : IsGraphon U μ) : kernelOp U μ (fun _ => 1) = degree U μ := by
  funext x; simp [kernelOp, degree]

omit [IsProbabilityMeasure μ] in
lemma degree_eq (x : Ω) : degree U μ x = edgeDensity U μ + degCentered U μ x := by simp [degCentered]

omit [IsProbabilityMeasure μ] in
lemma compressIter_zero : compressIter U μ 0 = degCentered U μ := rfl

omit [IsProbabilityMeasure μ] in
lemma degree_eq' (x : Ω) : degree U μ x = edgeDensity U μ + compressIter U μ 0 x := by rw [degree_eq, compressIter_zero]

lemma kernelOp_add' (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) (x : Ω) :
    kernelOp U μ (f + g) x = kernelOp U μ f x + kernelOp U μ g x := by
  simp only [kernelOp, Pi.add_apply]
  rw [← integral_add (integrable_Uf hU hf x) (integrable_Uf hU hg x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

omit [IsProbabilityMeasure μ] in
lemma kernelOp_smul' (c : ℝ) (f : Ω → ℝ) (x : Ω) : kernelOp U μ (c • f) x = c * kernelOp U μ f x := by
  simp only [kernelOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

lemma mean_kernelOp_compressIter (hU : IsGraphon U μ) (k : ℕ) :
    mean μ (kernelOp U μ (compressIter U μ k)) = specMoment U μ k := by
  have h1 : mean μ (kernelOp U μ (compressIter U μ k)) = ∫ x, kernelOp U μ (compressIter U μ k) x * 1 ∂μ := by simp [mean]
  rw [h1, kernelOp_symm hU (good_compressIter hU k) good_one, kernelOp_one hU]
  have hcongr : ∀ x, compressIter U μ k x * degree U μ x
      = edgeDensity U μ * compressIter U μ k x + degCentered U μ x * compressIter U μ k x := fun x => by rw [degree_eq]; ring
  rw [integral_congr_ae (ae_of_all _ hcongr),
    integral_add ((good_compressIter hU k).integrable.const_mul _) ((good_degCentered hU).mul (good_compressIter hU k)).integrable,
    integral_const_mul]
  have : ∫ x, compressIter U μ k x ∂μ = 0 := mean_compressIter hU k
  rw [this, mul_zero, zero_add]
  rfl

lemma kernelOp_compressIter (hU : IsGraphon U μ) (k : ℕ) :
    kernelOp U μ (compressIter U μ k) = fun x => specMoment U μ k + compressIter U μ (k + 1) x := by
  funext x
  have hdef : compressIter U μ (k + 1) x = kernelOp U μ (compressIter U μ k) x - mean μ (kernelOp U μ (compressIter U μ k)) := by
    simp only [compressIter, compress]
  rw [mean_kernelOp_compressIter hU k] at hdef
  linarith [hdef]

lemma kernelOp_compressIter' (hU : IsGraphon U μ) (k : ℕ) (x : Ω) :
    kernelOp U μ (compressIter U μ k) x = specMoment U μ k + compressIter U μ (k + 1) x := congrFun (kernelOp_compressIter hU k) x

noncomputable def pathIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (k + 1) => kernelOp U μ (pathIter U μ k)

noncomputable def pathDensity (U : Ω → Ω → ℝ) (μ : Measure Ω) (j : ℕ) : ℝ := mean μ (pathIter U μ j)

lemma mean_one : mean μ (fun _ : Ω => (1:ℝ)) = 1 := mean_const 1

omit [IsProbabilityMeasure μ] in
lemma mean_smul (c : ℝ) (f : Ω → ℝ) : mean μ (c • f) = c * mean μ f := by
  simp only [mean, Pi.smul_apply, smul_eq_mul]; rw [integral_const_mul]

lemma mean_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    mean μ (f + g) = mean μ f + mean μ g := by
  simp only [mean, Pi.add_apply]; exact integral_add hf.integrable hg.integrable

end OddCycleBound
