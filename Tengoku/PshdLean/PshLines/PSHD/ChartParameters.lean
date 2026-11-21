import Tengoku.PshdLean.PshLines.PSHD.NormalizedChart
import Tengoku.Seed.Analysis.InnerProductSpace.Orthogonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A bounded Euclidean region of radius--chart parameters

The parameter region for the bounded-chart proof of `pshd-vibe`, Lemma 1.3.
-/

open Set Metric

namespace PshLines.PSHD

/-- A maximum-metric ball supplies both admissible radii and bounded offsets.
@isnad1 id=and.1h3v.s7.64bc7368bb79 from=translated src=- shape=f20fe4bb vocab=97d0a680
-/
theorem chartParameter_ball_bounds {F : Type*} [NormedAddCommGroup F]
    {R : ℝ} {p : ℝ × F}
    (hp : p ∈ ball (3 * R / 4, (0 : F)) (min (R / 4) 1)) :
    R / 2 ≤ p.1 ∧ p.1 ≤ R ∧ ‖p.2‖ ≤ 1 := by
  have h := max_lt_iff.mp (show
    max (dist p.1 (3 * R / 4)) (dist p.2 0) < min (R / 4) 1 from hp)
  have hr := abs_lt.mp (show |p.1 - 3 * R / 4| < R / 4 from
    (h.1.trans_le (min_le_left _ _)))
  refine ⟨by linarith [hr.1], by linarith [hr.2], ?_⟩
  simpa using (h.2.trans_le (min_le_right _ _)).le

/-- Any circle-preserving chart map has a uniform lower distance bound on
the chosen parameter ball.
@isnad1 id=le.5h7v.s12.f3203d79e7f0 from=translated src=- shape=93fa2428 vocab=0db22325
-/
theorem chart_map_dist_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {e : E} (he : ‖e‖ = 1) {R : ℝ} (hR : 0 ≤ R) (x : E)
    {Ψ : ℝ × (ℂ ∙ e)ᗮ → E}
    (hcircle : ∀ p, ∃ z : ℂ,
      ‖z‖ = max (R / 2) (min R p.1) ∧
      Ψ p = x + z • NormedSpace.normalize (e + (p.2 : E)))
    {p q : ℝ × (ℂ ∙ e)ᗮ}
    (hp : p ∈ ball (3 * R / 4, 0) (min (R / 4) 1))
    (hq : q ∈ ball (3 * R / 4, 0) (min (R / 4) 1)) :
    min 1 (R / 4) * dist p q ≤ dist (Ψ p) (Ψ q) := by
  obtain ⟨hp0, hpR, hp1⟩ := chartParameter_ball_bounds hp
  obtain ⟨hq0, hqR, hq1⟩ := chartParameter_ball_bounds hq
  obtain ⟨z, hz, hzp⟩ := hcircle p
  obtain ⟨t, ht, htq⟩ := hcircle q
  simp only [min_eq_right hpR, max_eq_right hp0] at hz
  simp only [min_eq_right hqR, max_eq_right hq0] at ht
  have h := normalized_affineLift_max_lower_bound he
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.2.property)
    hp1 hq1 hR (by rw [hz]; exact hp0) (by rw [ht]; exact hq0)
  simpa [hzp, htq, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs, hz, ht] using h

end PshLines.PSHD
