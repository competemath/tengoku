import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.MonotoneProducts
import Tengoku.Seed.MeasureTheory.Function.L1Space.Integrable
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Integrable truncations of arbitrary extended nonnegative measurable inputs -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E]

/-- Cut off in space and in value at the same natural-number scale.-/
def boundedTruncation (f : E → ℝ≥0∞) (n : ℕ) : E → ℝ≥0∞ :=
  (Metric.closedBall 0 (n : ℝ)).indicator (fun x => min (f x) (n : ℝ≥0∞))

/--
@isnad1 id=le.0h4v.s4.159bfc1ced2d from=translated src=- shape=7cd7edd4 vocab=c5454ab5
-/
theorem boundedTruncation_le (f : E → ℝ≥0∞) (n : ℕ) (x : E) : boundedTruncation f n x ≤ f x := by
  classical
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · simpa only [boundedTruncation, indicator_of_mem hx] using min_le_left (f x) (n : ℝ≥0∞)
  · simp only [boundedTruncation, indicator_of_notMem hx, zero_le]

/--
@isnad1 id=le.0h4v.s4.489bc1c66d0d from=translated src=- shape=90fe4808 vocab=189d9332
-/
theorem boundedTruncation_le_nat (f : E → ℝ≥0∞) (n : ℕ) (x : E) :
    boundedTruncation f n x ≤ (n : ℝ≥0∞) := by
  classical
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · simpa only [boundedTruncation, indicator_of_mem hx] using min_le_right (f x) (n : ℝ≥0∞)
  · simp only [boundedTruncation, indicator_of_notMem hx, zero_le]

/--
@isnad1 id=ne.0h4v.s4.bbd5c69535fe from=translated src=- shape=1c2576d0 vocab=6c762703
-/
theorem boundedTruncation_ne_top (f : E → ℝ≥0∞) (n : ℕ) (x : E) :
    boundedTruncation f n x ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (boundedTruncation_le_nat f n x)

/--
@isnad1 id=monotone.0h3v.s4.8aa672266042 from=translated src=- shape=ad6934e5 vocab=4117373e
-/
theorem boundedTruncation_monotone (f : E → ℝ≥0∞) (x : E) :
    Monotone (fun n => boundedTruncation f n x) := by
  classical
  intro m n hmn
  by_cases hx : x ∈ Metric.closedBall 0 (m : ℝ)
  · have hyn : x ∈ Metric.closedBall 0 (n : ℝ) :=
      (Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)) hx
    simp only [boundedTruncation, indicator_of_mem hx, indicator_of_mem hyn]
    exact min_le_min_left _ (by exact_mod_cast hmn)
  · simp only [boundedTruncation, indicator_of_notMem hx, zero_le]

/--
@isnad1 id=tendsto.0h3v.s4.0035bfd519b1 from=translated src=- shape=d2948d91 vocab=81c987c7
-/
theorem boundedTruncation_tendsto (f : E → ℝ≥0∞) (x : E) :
    Tendsto (fun n => boundedTruncation f n x) atTop (𝓝 (f x)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ≥0∞)) atTop (𝓝 ⊤) := by
    simpa only [ENNReal.iSup_natCast] using tendsto_atTop_iSup
      (show Monotone (fun n : ℕ => (n : ℝ≥0∞)) from fun m n h => by
        change (m : ℝ≥0∞) ≤ (n : ℝ≥0∞)
        exact_mod_cast h)
  have hmin : Tendsto (fun n : ℕ => min (f x) (n : ℝ≥0∞)) atTop (𝓝 (f x)) := by
    have hc : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)) := tendsto_const_nhds
    simpa only [min_eq_left (show f x ≤ (⊤ : ℝ≥0∞) from le_top)] using hc.min hn
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  apply hmin.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x ∈ Metric.closedBall 0 (n : ℝ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hN.trans (by exact_mod_cast hn)
  simp only [boundedTruncation, indicator_of_mem hx]

/--
@isnad1 id=eq.0h3v.s5.7e854a71fd5b from=translated src=- shape=5aa71eb9 vocab=b4cd665d
-/
theorem iSup_boundedTruncation (f : E → ℝ≥0∞) (x : E) :
    (⨆ n, boundedTruncation f n x) = f x :=
  iSup_eq_of_tendsto (boundedTruncation_monotone f x) (boundedTruncation_tendsto f x)

variable [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=measurab.1h3v.s5.beb817c4284e from=translated src=- shape=90d5af34 vocab=ec2b0c12
-/
theorem boundedTruncation_measurable {f : E → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    Measurable (boundedTruncation f n) :=
  (hf.min measurable_const).indicator Metric.isClosed_closedBall.measurableSet

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Each truncation is a finite-valued integrable input to the real `L¹` theorem.
@isnad1 id=integrab.1h3v.s6.99b785597b0e from=translated src=- shape=12d9c7b7 vocab=ede5ff92
-/
theorem boundedTruncation_toReal_integrable {f : E → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    Integrable (fun x => (boundedTruncation f n x).toReal) := by
  have hb : (∫⁻ x, boundedTruncation f n x) ≤
      (n : ℝ≥0∞)*volume (Metric.closedBall (0 : E) (n : ℝ)) := by
    calc
      _ ≤ ∫⁻ x, (Metric.closedBall (0 : E) (n : ℝ)).indicator (fun _ => (n : ℝ≥0∞)) x := by
        apply lintegral_mono
        intro x
        classical
        by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
        · simpa only [indicator_of_mem hx] using boundedTruncation_le_nat f n x
        · simp only [boundedTruncation, indicator_of_notMem hx, le_refl]
      _ ≤ _ := lintegral_indicator_const_le _ _
  apply integrable_toReal_of_lintegral_ne_top (boundedTruncation_measurable hf n).aemeasurable
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) (isCompact_closedBall (0 : E) (n : ℝ)).measure_ne_top) hb

end GeometricBrascampLieb
