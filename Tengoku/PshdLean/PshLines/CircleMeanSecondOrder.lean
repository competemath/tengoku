import Tengoku.PshdLean.PshLines.SubmeanLaplacian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering the Laplacian from the circle submean inequality

For a C² function, the circle submean inequality at all sufficiently small
positive radii forces its actual Laplacian to be nonnegative at the center.
The proof uses a quadratic perturbation and the forward submean theorem:
subtracting `k * ‖z - c‖²` changes the Laplacian by `4 * k`, and changes the
circle mean by `k * R²`.
-/

noncomputable section

open Complex Filter Laplacian MeasureTheory Metric Real Set
open scoped Topology

namespace PshLines

/-- The ordinary Laplacian of a globally C² function on the complex plane is
continuous, with the normalization used in the complex-line Levi formula.
@isnad1 id=continuo.1h1v.s6.8c4b021461da from=translated src=- shape=8a05f8ab vocab=3a8128ab
-/
theorem continuous_laplacian_complex {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (Δ u) := by
  have hD : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have h₁ := (hD.clm_apply (continuous_const : Continuous (fun _ : ℂ ↦ (1 : ℂ)))).clm_apply
    (continuous_const : Continuous (fun _ : ℂ ↦ (1 : ℂ)))
  have hI := (hD.clm_apply (continuous_const : Continuous (fun _ : ℂ ↦ I))).clm_apply
    (continuous_const : Continuous (fun _ : ℂ ↦ I))
  simpa [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply] using! h₁.add hI

/-- The squared distance to the center has Laplacian four in the complex plane.
@isnad1 id=eq.0h2v.s6.d356892810a9 from=translated src=- shape=9805f95b vocab=9807756e
-/
theorem laplacian_complex_norm_sub_sq (c z : ℂ) :
    Δ (fun w : ℂ ↦ ‖w - c‖ ^ 2) z = 4 := by
  have h := laplacian_complexLine
    (u := fun w : ℂ ↦ ‖w‖ ^ 2)
    (contDiff_norm_sq ℂ) (-c) 1 z
  simpa [leviForm_norm_sq, sub_eq_add_neg, add_comm] using h

/-- Squared distance to the center is constant on a circle.
@isnad1 id=eq.0h2v.s6.724378faac31 from=translated src=- shape=bf9cc99f vocab=ee78b402
-/
theorem circleAverage_complex_norm_sub_sq (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun z : ℂ ↦ ‖z - c‖ ^ 2) c R = R ^ 2 := by
  calc
    Real.circleAverage (fun z : ℂ ↦ ‖z - c‖ ^ 2) c R =
        Real.circleAverage (fun _ : ℂ ↦ R ^ 2) c R := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hz' : ‖z - c‖ = |R| := by simpa only [mem_sphere, dist_eq_norm] using hz
      simp only [hz', sq_abs]
    _ = R ^ 2 := Real.circleAverage_const _ _ _

/-- A lower bound for the Laplacian gives the exact quadratic correction to the
circle submean inequality. The real constant `k` need not be positive.
@isnad1 id=le.3h4v.s7.162b5b2543da from=translated src=- shape=90919d53 vocab=bda9291a
-/
theorem quadratic_submean_of_laplacian_lower_bound {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℂ) {R k : ℝ} (hR : 0 ≤ R)
    (hΔ : ∀ z ∈ closedBall c R, 4 * k ≤ Δ u z) :
    u c + k * R ^ 2 ≤ Real.circleAverage u c R := by
  let q : ℂ → ℝ := fun z ↦ ‖z - c‖ ^ 2
  have hq : ContDiff ℝ 2 q := (contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)
  have hkq : ContDiff ℝ 2 (k • q) := hq.const_smul k
  have hmod : ContDiff ℝ 2 (u - k • q) := hu.sub hkq
  have hmodΔ : ∀ z ∈ closedBall c R, 0 ≤ Δ (u - k • q) z := by
    intro z hz
    rw [ContDiffAt.laplacian_sub (f₁ := u) (f₂ := k • q) hu.contDiffAt hkq.contDiffAt,
      InnerProductSpace.laplacian_smul (f := q) k hq.contDiffAt]
    change 0 ≤ Δ u z - k * Δ (fun w : ℂ ↦ ‖w - c‖ ^ 2) z
    rw [laplacian_complex_norm_sub_sq]
    linarith [hΔ z hz]
  have hm := submean_of_laplacian_nonneg (u := u - k • q) hmod c hR hmodΔ
  rw [Real.circleAverage_sub (ContinuousOn.circleIntegrable hR hu.continuous.continuousOn)
    (ContinuousOn.circleIntegrable hR hkq.continuous.continuousOn),
    Real.circleAverage_smul] at hm
  have hqmean : Real.circleAverage q c R = R ^ 2 := circleAverage_complex_norm_sub_sq c R
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hqmean, q,
    sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at hm
  linarith

/-- For a globally C² real function, the ordinary circle submean inequalities
at all sufficiently small positive radii force a nonnegative Laplacian at the
center. No differentiability property of circle averages is assumed.
@isnad1 id=le.2h2v.s7.764a5536358a from=translated src=- shape=1e5df453 vocab=ed250a0e
-/
theorem laplacian_nonneg_of_eventually_circleAverage_submean {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℂ)
    (hmean : ∀ᶠ r in 𝓝[>] (0 : ℝ), u c ≤ Real.circleAverage u c r) :
    0 ≤ Δ u c := by
  by_contra hnonneg
  have hneg : Δ u c < 0 := lt_of_not_ge hnonneg
  let k : ℝ := -Δ u c / 8
  have hk : 0 < k := by dsimp [k]; linarith
  have hkΔ : 4 * k < Δ (-u) c := by
    simp only [InnerProductSpace.laplacian_neg, Pi.neg_apply]
    dsimp [k]
    linarith
  have hnear : ∀ᶠ z in 𝓝 c, 4 * k < Δ (-u) z :=
    (continuous_laplacian_complex (u := -u) hu.neg).continuousAt.eventually
      (lt_mem_nhds hkΔ)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    nhdsWithin_le_nhds (gt_mem_nhds hδ)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hm, hrδ, hr⟩ := (hmean.and (hsmall.and hpos)).exists
  have hmod := quadratic_submean_of_laplacian_lower_bound (u := -u) hu.neg c hr.le
    (k := k) (fun z hz ↦ (hball (lt_of_le_of_lt (mem_closedBall.mp hz) hrδ)).le)
  have hmean_neg : Real.circleAverage (-u) c r = -Real.circleAverage u c r := by
    simpa only [neg_one_smul] using
      (Real.circleAverage_smul (f := u) (c := c) (R := r) (a := (-1 : ℝ)))
  rw [hmean_neg] at hmod
  have hstrict : 0 < k * r ^ 2 := mul_pos hk (sq_pos_of_pos hr)
  simp only [Pi.neg_apply] at hmod
  linarith

/-- A version with an explicit positive radius bound.
@isnad1 id=le.3h3v.s7.30b436448fa8 from=translated src=- shape=12076991 vocab=61719a9e
-/
theorem laplacian_nonneg_of_circleAverage_submean {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hmean : ∀ r ∈ Ioo 0 R, u c ≤ Real.circleAverage u c r) :
    0 ≤ Δ u c := by
  apply laplacian_nonneg_of_eventually_circleAverage_submean hu c
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R :=
    nhdsWithin_le_nhds (gt_mem_nhds hR)
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
  exact hmean r ⟨hr, hrR⟩

end PshLines
