import Tengoku.Seed.Topology.EMetricSpace.BoundedVariation
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! FTC and metric-variation bounds across finitely many nonsmooth points.
Continuity on the closed interval and integrability of the velocity are
retained; no derivative at the exceptional points is required. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory

theorem integral_eq_sub_of_hasDerivAt_off_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ v : ℝ → E) (T : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ T → HasDerivAt γ (v t) t)
    (hi : IntegrableOn v (Icc a b)) :
    (∫ t in a..b, v t) = γ b - γ a := by
  classical
  induction T using Finset.induction_on generalizing a b with
  | empty =>
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (fun t ht => hd t ht (Finset.notMem_empty t))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi)
  | @insert c T hcT ih =>
    by_cases hc' : c ∈ Ioo a b
    · have hiL := hi.mono_set (Icc_subset_Icc le_rfl hc'.2.le)
      have hiR := hi.mono_set (Icc_subset_Icc hc'.1.le le_rfl)
      have hL := ih hc'.1.le (hc.mono (Icc_subset_Icc le_rfl hc'.2.le))
        (fun t ht hT => hd t ⟨ht.1, ht.2.trans hc'.2⟩
          (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt ht.2, hT⟩)) hiL
      have hR := ih hc'.2.le (hc.mono (Icc_subset_Icc hc'.1.le le_rfl))
        (fun t ht hT => hd t ⟨hc'.1.trans ht.1, ht.2⟩
          (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt ht.1, hT⟩)) hiR
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hc'.1.le).mpr hiL)
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hc'.2.le).mpr hiR), hL, hR]
      abel
    · apply ih hab hc _ hi
      intro t ht hT
      exact hd t ht (by simp only [Finset.mem_insert, not_or]; exact ⟨fun htc => hc' (htc ▸ ht), hT⟩)

theorem integral_eq_sub_of_hasDerivAt_off_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ v : ℝ → E) (T : Set ℝ) (hT : T.Finite) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ T → HasDerivAt γ (v t) t)
    (hi : IntegrableOn v (Icc a b)) :
    (∫ t in a..b, v t) = γ b - γ a := by
  exact integral_eq_sub_of_hasDerivAt_off_finset γ v hT.toFinset hab hc
    (fun t ht hn => hd t ht (by simpa only [hT.mem_toFinset] using hn)) hi

theorem eVariationOn_le_integral_speed_off_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ v : ℝ → E) (T : Set ℝ) (hT : T.Finite) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ T → HasDerivAt γ (v t) t)
    (hi : IntegrableOn v (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ ENNReal.ofReal (∫ t in Icc a b, ‖v t‖) := by
  have hint {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      IntervalIntegrable v volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
      (hi.mono_set (Icc_subset_Icc hx.1 hy.2))
  have hdist {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      ‖γ y - γ x‖ ≤ ∫ t in x..y, ‖v t‖ := by
    rw [← integral_eq_sub_of_hasDerivAt_off_finite γ v T hT hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun t ht => hd t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩) (hi.mono_set (Icc_subset_Icc hx.1 hy.2))]
    exact intervalIntegral.norm_integral_le_integral_norm hxy
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hmem⟩
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), ‖v t‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (hdist (hmem i) (hmem (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∫ t in u 0..u n, ‖v t‖) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ => norm_nonneg _))]
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => (hint (hmem i) (hmem (i + 1)) (hu (Nat.le_succ i))).norm)]
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖v t‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hmem 0).1 (hu (Nat.zero_le n)) (hmem n).2
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi).norm
    _ = _ := by rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

end
end DuistermaatVanDerKallen
