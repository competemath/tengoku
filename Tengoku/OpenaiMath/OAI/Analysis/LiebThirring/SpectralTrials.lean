import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.FlagApproximation

namespace OAI

universe u179

noncomputable section
namespace SharpLiebThirring.SpectralProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set ContinuationGap ActionProof
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma triangular_action_upper {σ l r : ℝ} (hσ : 0 < σ) (hlr : l ≤ r)
    (k : Fin N → ℝ) (a v : ℝ → Fin N → ℝ)
    (ha : ContinuousOn a (Icc l r)) (hv : ContinuousOn v (Icc l r))
    {W : ℝ → ℝ} (hW : IntervalIntegrable W volume l r)
    (hWn : ∀ᵐ x ∂volume, 0 ≤ W x)
    (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (he : (∫ t in l..r, (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) ≤
      ∫ t in l..r, W t*(∑ i, a t i^2)) :
    (∫ t in l..r, actionDensity σ k (a t) (v t)) ≤
      actionYoungConstant σ * ∫ t, W t^(1+σ) := by
  let m := fun t ↦ ∑ i, a t i^2
  have hm : ContinuousOn m (Icc l r) := continuousOn_finsetSum Finset.univ (fun i _ ↦ (continuousOn_pi.mp ha i).pow 2)
  have hm0 (t : ℝ) : 0 ≤ m t := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmr : ContinuousOn (fun t ↦ m t^(1+1/σ)) (Icc l r) :=
    hm.rpow_const (fun _ _ ↦ Or.inr (by positivity))
  have hE : ContinuousOn (fun t ↦ (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) (Icc l r) :=
    (continuousOn_finsetSum Finset.univ (fun i _ ↦ (continuousOn_pi.mp hv i).pow 2)).add
      (continuousOn_finsetSum Finset.univ (fun i _ ↦ ((continuousOn_pi.mp ha i).pow 2).const_mul _))
  have hEi : IntervalIntegrable (fun t ↦ (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) volume l r := hE.intervalIntegrable_of_Icc hlr
  have hmri : IntervalIntegrable (fun t ↦ m t^(1+1/σ)) volume l r := hmr.intervalIntegrable_of_Icc hlr
  have hWmi : IntervalIntegrable (fun t ↦ W t*m t) volume l r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlr] at hW ⊢
    exact hW.mul_continuousOn hm isCompact_Icc
  have hAi : IntervalIntegrable (fun t ↦ actionYoungConstant σ * W t^(1+σ)) volume l r := hWp.intervalIntegrable.const_mul (actionYoungConstant σ)
  calc
    (∫ t in l..r, actionDensity σ k (a t) (v t)) =
        (∫ t in l..r, (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) -
          ∫ t in l..r, m t^(1+1/σ) := intervalIntegral.integral_sub hEi hmri
    _ ≤ (∫ t in l..r, W t*m t) - ∫ t in l..r, m t^(1+1/σ) := sub_le_sub_right he _
    _ = ∫ t in l..r, W t*m t-m t^(1+1/σ) :=
      (intervalIntegral.integral_sub hWmi hmri).symm
    _ ≤ ∫ t in l..r, actionYoungConstant σ * W t^(1+σ) := by
      apply intervalIntegral.integral_mono_ae_restrict hlr (hWmi.sub hmri) hAi
      filter_upwards [ae_restrict_of_ae hWn] with t ht
      exact young_action_bound hσ ht (hm0 t)
    _ = actionYoungConstant σ * ∫ t in l..r, W t^(1+σ) := intervalIntegral.integral_const_mul _ _
    _ ≤ actionYoungConstant σ * ∫ t, W t^(1+σ) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold actionYoungConstant; positivity)
      rw [intervalIntegral.integral_of_le hlr]
      exact integral_mono_measure Measure.restrict_le_self
        (hWn.mono fun x hx ↦ Real.rpow_nonneg hx _) hWp

end SharpLiebThirring.SpectralProof

end

noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Filter Matrix MatrixProof ContinuationGap
open scoped Topology Matrix.Norms.L2Operator

lemma compact_family_radius {ι : Type u179} [Fintype ι] (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) :
    ∃ R : ℝ, 0 < R ∧ ∀ i x, R ≤ |x| → (u i).val x = 0 ∧ (u i).grad x = 0 := by
  have hc : IsCompact (⋃ i, tsupport (u i).val) := isCompact_iUnion hu
  obtain ⟨R,hR,hs⟩ := hc.isBounded.subset_ball_lt 0 0
  refine ⟨R,hR,fun i x hx ↦ ?_⟩
  have hn : x ∉ tsupport (u i).val := by
    intro hm
    have hxb := hs (mem_iUnion.2 ⟨i,hm⟩)
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] at hxb
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hn,?_⟩
  rw [← deriv_val]
  apply Function.notMem_support.mp
  exact fun hd ↦ hn (support_deriv_subset hd)

lemma integral_eq_interval_of_vanish {R : ℝ} (_hR : 0 ≤ R) {f : ℝ → ℝ}
    (hf : ∀ x, R ≤ |x| → f x = 0) : (∫ x, f x) = ∫ x in -R..R, f x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hn : |x| < R := lt_of_not_ge (fun h ↦ hx (hf x h))
  exact ⟨by rw [abs_lt] at hn; linarith [hn.1],by rw [abs_lt] at hn; linarith [hn.2]⟩

end SharpLiebThirring.SpectralProof

end

end OAI
