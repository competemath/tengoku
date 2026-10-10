import Tengoku.OpenaiMath.OAI.Analysis.DirectCrouzeix.HarmonicReflection

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

def logModulusUpper (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < z.im then Real.log ‖f z‖ else 0

theorem logModulusUpper_real {f : ℂ → ℂ} {z : ℂ} (hz : z.im = 0) :
    logModulusUpper f z = 0 := by simp [logModulusUpper, hz]

theorem logModulusUpper_continuous {R : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ContinuousOn (logModulusUpper f) (upperClosedBall R) := by
  unfold logModulusUpper
  apply ContinuousOn.if'
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    have ht : Tendsto (fun w => Real.log ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp (hl z hz.1.1 hz0)
    exact ht.mono_left (nhdsWithin_mono _ inter_subset_right)
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    exact tendsto_const_nhds
  · apply (hc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))).mono
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  · exact continuousOn_const

theorem upperBall_convex (R : ℝ) : Convex ℝ (upperBall R) :=
  (convex_ball (0 : ℂ) R).inter (convex_Ioi (0 : ℝ) |>.linear_preimage Complex.imCLM.toLinearMap)

theorem upperBall_half_radius {R : ℝ} (hR : 0 < R) :
    ((R / 2 : ℝ) : ℂ) * Complex.I ∈ upperBall R := by
  constructor
  · simp only [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hR)]
    linarith
  · simpa using half_pos hR

theorem circleAverage_pos_upper {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, 0 ≤ u z) (hp : 0 < u ((R : ℂ) * Complex.I)) :
    0 < Real.circleAverage u 0 R := by
  have hall (θ : ℝ) : circleMap 0 R θ ∈ sphere 0 R := by
    simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
  have hc : Continuous (fun θ => u (circleMap 0 R θ)) :=
    hu.comp_continuous (continuous_circleMap 0 R) hall
  have hip : 0 < ∫ θ in (0 : ℝ)..2 * Real.pi, u (circleMap 0 R θ) := by
    apply intervalIntegral.integral_pos Real.two_pi_pos hc.continuousOn
    · intro θ _
      exact hn _ (hall θ)
    · refine ⟨Real.pi / 2, ⟨by positivity, by nlinarith [Real.pi_pos]⟩, ?_⟩
      simpa only [circleMap_pi_div_two, zero_add] using hp
  exact mul_pos (inv_pos.mpr Real.two_pi_pos) hip

end Conformal

end DirectCrouzeix

end

end

end

end OAI
