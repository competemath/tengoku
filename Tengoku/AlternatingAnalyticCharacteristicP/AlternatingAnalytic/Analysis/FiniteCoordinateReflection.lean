import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.ClosedSubspaceCoefficients
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteCoordinateLift
import Tengoku.Seed.Analysis.Analytic.Within

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-coordinate analytic reflection

Let `j : F → G` be a closed linear isometry and let the parameter space be boundedly
isomorphic to `K^d`. Then `f` is analytic if and only if `j ∘ f` is (Theorem 4.4).
Neither the field nor the spaces need be complete.
-/

noncomputable section

open scoped Topology NNReal ENNReal

namespace AlternatingAnalytic

variable {K E F G : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup G] [NormedSpace K G]

/-- Exponentially increasing the coefficient norms preserves a positive radius.
@isnad1 id=lt.3h7v.s8.d51872712cb1 from=translated src=- shape=f3d0f08f vocab=4021cd79
-/
theorem radius_pos_of_exponential_bound
    {p : FormalMultilinearSeries K E F} {q : FormalMultilinearSeries K E G}
    (hp : 0 < p.radius) {a : ℝ} (ha : 0 ≤ a)
    (hq : ∀ n, ‖q n‖ ≤ a ^ n * ‖p n‖) : 0 < q.radius := by
  obtain ⟨C, r, hC, hr, hpr⟩ := p.le_mul_pow_of_radius_pos hp
  let b : ℝ := (a + 1) * r
  have hb : 0 < b := mul_pos (by positivity) hr
  let s : ℝ≥0 := ⟨b⁻¹, (inv_pos.mpr hb).le⟩
  have hs : (0 : ℝ≥0∞) < s := by
    exact_mod_cast (inv_pos.mpr hb)
  refine hs.trans_le (q.le_radius_of_bound C fun n => ?_)
  calc
    ‖q n‖ * (s : ℝ) ^ n ≤ (a ^ n * (C * r ^ n)) * (b⁻¹) ^ n := by
      exact mul_le_mul_of_nonneg_right
        ((hq n).trans (mul_le_mul_of_nonneg_left (hpr n) (pow_nonneg ha n)))
        (pow_nonneg (inv_pos.mpr hb).le n)
    _ ≤ ((a + 1) ^ n * (C * r ^ n)) * (b⁻¹) ^ n := by
      gcongr
      linarith
    _ = C := by
      rw [show (a + 1) ^ n * (C * r ^ n) = C * b ^ n by
        dsimp only [b]
        rw [mul_pow]
        ring]
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hb.ne', one_pow, mul_one]

/-- A subspace-valued series with the same diagonals and coefficients bounded by
`a ^ n ‖p n‖` makes `f` analytic.
@isnad1 id=analytic.4h9v.s11.460c4f3f23b9 from=translated src=- shape=9480093b vocab=b4e29c7f
-/
theorem analyticAt_of_subspace_series
    (W : Submodule K F) {f : E → W} {x : E}
    {p : FormalMultilinearSeries K E F}
    (hp : HasFPowerSeriesAt (fun y => (f y : F)) p x)
    (q : FormalMultilinearSeries K E W) {a : ℝ} (ha : 0 ≤ a)
    (hq : ∀ n, ‖q n‖ ≤ a ^ n * ‖p n‖)
    (hdiag : ∀ n y, (q n (fun _ => y) : F) = p n (fun _ => y)) :
    AnalyticAt K f x := by
  have hqpos := radius_pos_of_exponential_bound hp.radius_pos ha hq
  obtain ⟨r, hr⟩ := hp
  refine ⟨q, min r q.radius, min_le_right _ _, lt_min hr.r_pos hqpos, ?_⟩
  intro y hy
  have hsum := hr.hasSum (Metric.eball_subset_eball (min_le_left _ _) hy)
  apply (W.subtypeₗᵢ.isEmbedding.isInducing.hasSum_iff
    (g := W.subtypeL) (fun n => q n (fun _ => y)) (f (x + y))).mp
  change HasSum (fun n => (q n (fun _ => y) : F)) (f (x + y) : F)
  simpa only [hdiag] using hsum

end AlternatingAnalytic
