import Tengoku.PshdLean.PshLines.PSHD.RieszEnergy
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Integral
import Tengoku.Seed.MeasureTheory.Group.LIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite Riesz energy on bounded Euclidean sets

The radial integrability input in `pshd-vibe`, Lemma 1.3.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The singular Riesz kernel is integrable on every ball below ambient dimension.
@isnad1 id=lt.2h4v.s7.5b60b459541c from=translated src=- shape=64708539 vocab=b7f32397
-/
theorem lintegral_rieszKernel_ball_lt_top {s : ℝ}
    (hs : 0 < s) (hd : s < Module.finrank ℝ E) (R : ℝ) :
    (∫⁻ x in ball (0 : E) R, (edist x 0 ^ s)⁻¹ ∂μ) < ⊤ := by
  have hdim : 1 ≤ Module.finrank ℝ E := by
    have : (0 : ℝ) < Module.finrank ℝ E := hs.trans hd
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt this)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hdim
  have hi : IntegrableOn (fun x : E ↦ ‖x‖ ^ (-s)) (ball 0 R) μ :=
    integrableOn_ball_of_norm_le_rpow hdim hd (C := 1)
      (Filter.Eventually.of_forall (by intro x; simp [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]))
      ((measurable_norm.pow_const (-s)).aestronglyMeasurable)
  have heq : (fun x : E ↦ (edist x 0 ^ s)⁻¹) =ᵐ[μ.restrict (ball 0 R)]
      (fun x : E ↦ ENNReal.ofReal (‖x‖ ^ (-s))) := by
    filter_upwards [ae_restrict_of_ae (μ.ae_ne (0 : E))] with x hx
    rw [edist_dist, dist_zero_right, ← ENNReal.rpow_neg,
      ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hx)]
  rw [lintegral_congr_ae heq]
  exact hi.lintegral_lt_top

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A uniform bound on the potential of the restriction of Haar measure to a ball.
@isnad1 id=le.1h6v.s7.c04162aa118b from=translated src=- shape=5d63706b vocab=c040e7b4
-/
theorem lintegral_rieszKernel_ball_le (s : ℝ) {c x : E} {R : ℝ}
    (hx : x ∈ ball c R) :
    (∫⁻ y in ball c R, (edist x y ^ s)⁻¹ ∂μ) ≤
      ∫⁻ z in ball (0 : E) (2 * R), (edist z 0 ^ s)⁻¹ ∂μ := by
  rw [← lintegral_indicator measurableSet_ball]
  calc
    _ ≤ ∫⁻ y, (ball (0 : E) (2 * R)).indicator
        (fun z ↦ (edist z 0 ^ s)⁻¹) (y - x) ∂μ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ ball c R
      · have hxy : y - x ∈ ball (0 : E) (2 * R) := by
          rw [mem_ball, dist_zero_right, ← dist_eq_norm]
          calc
            dist y x ≤ dist y c + dist x c := dist_triangle_right y x c
            _ < 2 * R := by linarith [mem_ball.mp hx, mem_ball.mp hy]
        simp only [indicator_of_mem hy, indicator_of_mem hxy]
        simp [edist_dist, dist_eq_norm, norm_sub_rev]
      · simp only [indicator_of_notMem hy]
        exact bot_le
    _ = _ := by rw [lintegral_sub_right_eq_self, lintegral_indicator measurableSet_ball]

/-- Haar measure restricted to any bounded ball has finite subdimensional Riesz energy.
@isnad1 id=lt.2h5v.s7.b94f6a053f89 from=translated src=- shape=6b3f5e01 vocab=63364cb0
-/
theorem rieszEnergy_restrict_ball_lt_top {s : ℝ}
    (hs : 0 < s) (hd : s < Module.finrank ℝ E) (c : E) (R : ℝ) :
    rieszEnergy s (μ.restrict (ball c R)) < ⊤ := by
  unfold rieszEnergy
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _x in ball c R,
        (∫⁻ z in ball (0 : E) (2 * R), (edist z 0 ^ s)⁻¹ ∂μ) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
      exact lintegral_rieszKernel_ball_le s hx
    _ < ⊤ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top (lintegral_rieszKernel_ball_lt_top hs hd _) measure_ball_lt_top

/-- Normalizing Haar measure on a positive-radius ball gives a probability
carried by that ball with finite subdimensional Riesz energy.
@isnad1 id=other.3h5v.s7.1c5da86674b9 from=translated src=- shape=78e5c32f vocab=7cb7355a
-/
theorem normalized_restrict_ball_properties {s : ℝ}
    (hs : 0 < s) (hd : s < Module.finrank ℝ E) (c : E) {R : ℝ} (hR : 0 < R) :
    let m := (μ (ball c R))⁻¹ • μ.restrict (ball c R)
    IsProbabilityMeasure m ∧ m (ball c R) = 1 ∧ rieszEnergy s m < ⊤ := by
  have hpos : μ (ball c R) ≠ 0 := (measure_ball_pos μ c hR).ne'
  have hfin : μ (ball c R) ≠ ⊤ := measure_ball_lt_top.ne
  have hmass : (μ (ball c R))⁻¹ * μ (ball c R) = 1 :=
    ENNReal.inv_mul_cancel hpos hfin
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simpa only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul] using hmass
  · simpa only [Measure.smul_apply, Measure.restrict_apply measurableSet_ball,
      inter_self, smul_eq_mul] using hmass
  · rw [rieszEnergy_smul]
    exact ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hpos)))
      (rieszEnergy_restrict_ball_lt_top hs hd c R)

end PshLines.PSHD
