import Tengoku.Piirrationalitymeasure.Formalization.GaussianPowerLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Extending a local Gaussian modulus bound over a compact integration interval. -/

namespace PiIrrationality

open Filter
open scoped Topology

/--
@isnad1 id=ex.3h2v.s6.d3b5640c33d4 from=translated src=- shape=ca4d1ac9 vocab=87accc9f
-/
theorem compact_positive_norm_bound {K : Set ℝ} {f : ℝ → ℂ}
    (hK : IsCompact K) (hf : ContinuousOn f K) (h : ∀ t ∈ K, ‖f t‖ < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ t ∈ K, ‖f t‖ ≤ q := by
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    simp [he]
  obtain ⟨t, ht, hmax⟩ := hK.exists_isMaxOn hne hf.norm
  refine ⟨(‖f t‖ + 1) / 2, by positivity, by linarith [h t ht], ?_⟩
  intro s hs
  have hm := hmax hs
  change ‖f s‖ ≤ ‖f t‖ at hm
  linarith [h t ht]

/--
@isnad1 id=ex.5h3v.s7.d93f44a82d1e from=translated src=- shape=615c86ad vocab=90657044
-/
theorem local_gaussian_global_bound {f : ℝ → ℂ} {T k : ℝ} (hT : 0 < T) (hk : 0 < k)
    (hf : ContinuousOn f (Set.Icc (-T) T))
    (hstrict : ∀ t ∈ Set.Icc (-T) T, t ≠ 0 → ‖f t‖ < 1)
    (hloc : ∀ᶠ t : ℝ in 𝓝 0, ‖f t‖ ≤ Real.exp (-k * t ^ 2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Icc (-T) T, ‖f t‖ ≤ Real.exp (-c * t ^ 2) := by
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hloc
  let K : Set ℝ := Set.Icc (-T) T ∩ {t : ℝ | δ / 2 ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hKsub : K ⊆ Set.Icc (-T) T := Set.inter_subset_left
  obtain ⟨q, hq0, hq1, hq⟩ := compact_positive_norm_bound hK (hf.mono hKsub) (by
    intro t ht
    apply hstrict t ht.1
    intro he
    have hb := ht.2
    change δ / 2 ≤ |t| at hb
    simp only [he, abs_zero] at hb
    linarith)
  have hlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  let c := min k (-Real.log q / T ^ 2)
  have hc : 0 < c := lt_min hk (div_pos hlog (pow_pos hT _))
  refine ⟨c, hc, fun t ht => ?_⟩
  by_cases hsmall : |t| < δ
  · have hb := hd (y := t) (by simpa only [Real.dist_eq, sub_zero] using hsmall)
    apply hb.trans
    apply Real.exp_le_exp.mpr
    have hck : c ≤ k := min_le_left _ _
    nlinarith [sq_nonneg t]
  · have htK : t ∈ K := ⟨ht, by dsimp; linarith [le_of_not_gt hsmall]⟩
    apply (hq t htK).trans
    rw [← Real.exp_log hq0]
    apply Real.exp_le_exp.mpr
    have hct : c * T ^ 2 ≤ -Real.log q :=
      (le_div_iff₀ (pow_pos hT 2)).mp (min_le_right k (-Real.log q / T ^ 2))
    have htT : t ^ 2 ≤ T ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) hT.le).mpr (abs_le.mpr ht)
    nlinarith [mul_le_mul_of_nonneg_left htT hc.le]

end PiIrrationality
