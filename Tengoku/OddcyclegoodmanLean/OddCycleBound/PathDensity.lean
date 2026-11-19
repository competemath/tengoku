import Tengoku.OddcyclegoodmanLean.OddCycleBound.Graphon

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/--
@isnad1 id=good.0h1v.s4.eda99a38f445 from=translated src=- shape=9d21b14e vocab=48def5ae
-/
lemma good_one : Good (fun _ : Ω => (1 : ℝ)) :=
  ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

/--
@isnad1 id=good.1h3v.s5.a1073a0cf479 from=translated src=- shape=d4ac94bc vocab=7f675b08
-/
lemma good_smul (c : ℝ) {f : Ω → ℝ} (hf : Good f) : Good (c • f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.const_smul c, ⟨|c| * C, mul_nonneg (abs_nonneg _) hC0, fun x => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

/--
@isnad1 id=good.2h3v.s5.b950aa2d876b from=translated src=- shape=634321c7 vocab=38ea8197
-/
lemma good_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f + g) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨hf.meas.add hg.meas, ⟨Cf + Cg, by linarith, fun x => ?_⟩⟩
  rw [Pi.add_apply]
  exact (abs_add_le _ _).trans (by linarith [hCf x, hCg x])

/--
@isnad1 id=integrab.2h5v.s6.b1c92244d7ea from=translated src=- shape=3c228969 vocab=30a8f0ec
-/
lemma integrable_Uf (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    Integrable (fun y => U x y * f y) μ := by
  have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
  exact (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.1h3v.s5.01e597858032 from=translated src=- shape=2a1709db vocab=7524f4f6
-/
lemma kernelOp_one (_hU : IsGraphon U μ) : kernelOp U μ (fun _ => 1) = degree U μ := by
  funext x; simp [kernelOp, degree]

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.0h4v.s5.689b7a032dee from=translated src=- shape=136ed58e vocab=c47988cb
-/
lemma degree_eq (x : Ω) : degree U μ x = edgeDensity U μ + degCentered U μ x := by simp [degCentered]

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.0h3v.s5.cc79e82d8261 from=translated src=- shape=d5b77db1 vocab=28fbfcbb
-/
lemma compressIter_zero : compressIter U μ 0 = degCentered U μ := rfl

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.0h4v.s5.c404f81ed290 from=translated src=- shape=3a7271d4 vocab=b7a0ee33
-/
lemma degree_eq' (x : Ω) : degree U μ x = edgeDensity U μ + compressIter U μ 0 x := by rw [degree_eq, compressIter_zero]

/--
@isnad1 id=eq.3h6v.s6.c207dc0096da from=translated src=- shape=2ff8c087 vocab=1b805919
-/
lemma kernelOp_add' (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) (x : Ω) :
    kernelOp U μ (f + g) x = kernelOp U μ f x + kernelOp U μ g x := by
  simp only [kernelOp, Pi.add_apply]
  rw [← integral_add (integrable_Uf hU hf x) (integrable_Uf hU hg x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.0h6v.s6.f04067ec736a from=translated src=- shape=17657479 vocab=2217cdcf
-/
lemma kernelOp_smul' (c : ℝ) (f : Ω → ℝ) (x : Ω) : kernelOp U μ (c • f) x = c * kernelOp U μ f x := by
  simp only [kernelOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/--
@isnad1 id=eq.1h4v.s5.0b1d861d2793 from=translated src=- shape=5db15ae3 vocab=7ec35d45
-/
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

/--
@isnad1 id=eq.1h4v.s6.dc2f0b51adf3 from=translated src=- shape=24d539e9 vocab=5a212563
-/
lemma kernelOp_compressIter (hU : IsGraphon U μ) (k : ℕ) :
    kernelOp U μ (compressIter U μ k) = fun x => specMoment U μ k + compressIter U μ (k + 1) x := by
  funext x
  have hdef : compressIter U μ (k + 1) x = kernelOp U μ (compressIter U μ k) x - mean μ (kernelOp U μ (compressIter U μ k)) := by
    simp only [compressIter, compress]
  rw [mean_kernelOp_compressIter hU k] at hdef
  linarith [hdef]

/--
@isnad1 id=eq.1h5v.s6.8dfa0a08fe59 from=translated src=- shape=7a9bd1cd vocab=5a212563
-/
lemma kernelOp_compressIter' (hU : IsGraphon U μ) (k : ℕ) (x : Ω) :
    kernelOp U μ (compressIter U μ k) x = specMoment U μ k + compressIter U μ (k + 1) x := congrFun (kernelOp_compressIter hU k) x

noncomputable def pathIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (k + 1) => kernelOp U μ (pathIter U μ k)

noncomputable def pathDensity (U : Ω → Ω → ℝ) (μ : Measure Ω) (j : ℕ) : ℝ := mean μ (pathIter U μ j)

/--
@isnad1 id=eq.0h2v.s5.917d773ecbb0 from=translated src=- shape=aa34cffe vocab=03b73225
-/
lemma mean_one : mean μ (fun _ : Ω => (1:ℝ)) = 1 := mean_const 1

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=eq.0h4v.s5.0e37434e7605 from=translated src=- shape=7528036d vocab=753c3a53
-/
lemma mean_smul (c : ℝ) (f : Ω → ℝ) : mean μ (c • f) = c * mean μ f := by
  simp only [mean, Pi.smul_apply, smul_eq_mul]; rw [integral_const_mul]

/--
@isnad1 id=eq.2h4v.s6.40aa28d844ea from=translated src=- shape=ea49de05 vocab=33279875
-/
lemma mean_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    mean μ (f + g) = mean μ f + mean μ g := by
  simp only [mean, Pi.add_apply]; exact integral_add hf.integrable hg.integrable

end OddCycleBound
