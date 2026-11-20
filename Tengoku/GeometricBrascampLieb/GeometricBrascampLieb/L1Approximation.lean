import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ContinuousCompact
import Tengoku.Seed.MeasureTheory.Function.ContinuousMapDense
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Nonnegative continuous compact approximations with almost-everywhere convergence -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=ex.3h3v.s8.f223cc94cf4b from=translated src=- shape=acc203a6 vocab=121fe211
-/
theorem exists_nonneg_compact_approx {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, 0 ≤ g x) ∧
      Integrable g ∧ (∫ x, ‖f x-g x‖) ≤ ε := by
  obtain ⟨g, hgc, herr, hgcont, hgi⟩ := hf.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨fun x => |g x|, hgcont.abs, hgc.abs, fun x => abs_nonneg _, hgi.norm, ?_⟩
  have hpoint (x : E) : ‖f x-|g x|‖ ≤ ‖f x-g x‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using abs_norm_sub_norm_le (f x) (g x)
  exact (integral_mono (hf.sub hgi.norm).norm (hf.sub hgi).norm hpoint).trans herr

/-- Nonnegative `L¹` data admit compact continuous approximations converging a.e. and in mass.
@isnad1 id=ex.2h2v.s8.e8a9068ae35d from=translated src=- shape=4f5722cb vocab=82413925
-/
theorem exists_nonneg_compact_approximation {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∃ g : ℕ → E → ℝ, (∀ n, Continuous (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n x, 0 ≤ g n x) ∧
      (∀ᵐ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) ∧
      Tendsto (fun n => ∫ x, g n x) atTop (𝓝 (∫ x, f x)) := by
  have he (n : ℕ) : 0 < 1/((n : ℝ)+1) := by positivity
  choose g hgc hgcompact hg0 hgi herror using fun n => exists_nonneg_compact_approx hf hf0 (he n)
  have hb (n : ℕ) : (∫ x, ‖g n x-f x‖) ≤ 1/((n : ℝ)+1) := by
    simpa only [norm_sub_rev] using herror n
  have hL : Tendsto (fun n => ∫ x, ‖g n x-f x‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hb
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hLp : Tendsto (fun n => eLpNorm (g n-f) 1) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hL
    simp only [ENNReal.ofReal_zero] at h
    convert h using 1
    ext n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hgi n).sub hf)]
    rfl
  have hmass : Tendsto (fun n => ∫ x, g n x) atTop (𝓝 (∫ x, f x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) hL
    rw [← integral_sub (hgi n) hf]
    exact norm_integral_le_integral_norm _
  obtain ⟨s, hs, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n => (hgi n).aestronglyMeasurable) hf.aestronglyMeasurable hLp).exists_seq_tendsto_ae
  exact ⟨fun n => g (s n), fun n => hgc _, fun n => hgcompact _, fun n => hg0 _, hae,
    hmass.comp hs.tendsto_atTop⟩

end GeometricBrascampLieb
