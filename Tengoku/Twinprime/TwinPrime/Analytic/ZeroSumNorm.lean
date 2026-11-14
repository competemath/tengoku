import Tengoku.Twinprime.TwinPrime.Analytic.ZeroFactorBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norm bounds for the actual local zero sum

The finite analytic divisor has nonnegative multiplicities. Separation
from every zero bounds its reciprocal sum by total multiplicity divided
by the separation. A zero-free rectangle supplies that separation even
when the evaluation point is left of the line Re(s)=1.
-/

noncomputable section

open Metric MeromorphicOn Finset

namespace TwinPrime.Analytic

theorem norm_divisor_zero_sum_le {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K)
    (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ u : ℂ, divisor f K u ≠ 0 → δ ≤ ‖s - u‖) :
    ‖∑ᶠ u, (divisor f K u : ℂ) / (s - u)‖ ≤
      (((∑ᶠ u, divisor f K u) : ℤ) : ℝ) / δ := by
  classical
  let S := ((divisor f K).finiteSupport hK).toFinset
  have hsum : (∑ᶠ u, (divisor f K u : ℂ) / (s - u)) =
      ∑ u ∈ S, (divisor f K u : ℂ) / (s - u) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    have hD : divisor f K u ≠ 0 := by
      intro he
      exact hu (by simp [he])
    simpa [S] using hD
  have hDsum : (((∑ᶠ u, divisor f K u) : ℤ) : ℝ) =
      ∑ u ∈ S, (divisor f K u : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _
      (by simp [S] : (divisor f K).support ⊆ S)]
    push_cast
    rfl
  rw [hsum, hDsum]
  apply (norm_sum_le _ _).trans
  rw [sum_div]
  apply sum_le_sum
  intro u hu
  have hD : divisor f K u ≠ 0 := by simpa [S] using hu
  have hD0 : (0 : ℝ) ≤ divisor f K u := by exact_mod_cast hf.divisor_nonneg u
  have hn : ‖(divisor f K u : ℂ)‖ = (divisor f K u : ℝ) := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD0]
  rw [norm_div, hn]
  exact div_le_div_of_nonneg_left hD0 hδ (hsep u hD)

theorem analytic_zero_of_divisor_ne_zero {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (u : ℂ) (hu : divisor f K u ≠ 0) : f u = 0 := by
  have hmem : u ∈ K := (divisor f K).supportWithinDomain hu
  by_contra hzero
  have ho := (hf u hmem).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hzero
  rw [divisor_apply hf.meromorphicOn hmem, ho] at hu
  simp at hu

/-- The height margin covers the entire local divisor disk.-/
theorem abs_im_le_height_add_two_of_mem_local_disk (H : ℝ) (c u : ℂ)
    (hc : |c.im| ≤ H) (hu : u ∈ closedBall c (5 / 4)) : |u.im| ≤ H + 2 := by
  have hdiff : |u.im - c.im| ≤ 5 / 4 := by
    have h := Complex.abs_im_le_norm (u - c)
    simp only [Complex.sub_im] at h
    exact h.trans (mem_closedBall_iff_norm.mp hu)
  have htri : |u.im| ≤ |u.im - c.im| + |c.im| := by
    simpa only [sub_add_cancel] using abs_add_le (u.im - c.im) c.im
  linarith

theorem divisor_zero_separation_of_zero_free_rectangle {f : ℂ → ℂ}
    (c s : ℂ) (δ H : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall c (5 / 4)))
    (hc : |c.im| ≤ H) (hs : 1 - δ ≤ s.re)
    (hfree : ∀ u : ℂ, 1 - 2 * δ ≤ u.re → |u.im| ≤ H + 2 → f u ≠ 0)
    (u : ℂ) (hu : divisor f (closedBall c (5 / 4)) u ≠ 0) : δ ≤ ‖s - u‖ := by
  have humem : u ∈ closedBall c (5 / 4) :=
    (divisor f (closedBall c (5 / 4))).supportWithinDomain hu
  have him := abs_im_le_height_add_two_of_mem_local_disk H c u hc humem
  have hzero := analytic_zero_of_divisor_ne_zero hf u hu
  have hre : u.re < 1 - 2 * δ := by
    by_contra h
    exact hfree u (not_lt.mp h) him hzero
  have hnorm := Complex.re_le_norm (s - u)
  simp only [Complex.sub_re] at hnorm
  linarith

theorem norm_divisor_zero_sum_le_of_zero_free_rectangle {f : ℂ → ℂ}
    (c s : ℂ) (δ H : ℝ) (hδ : 0 < δ)
    (hf : AnalyticOnNhd ℂ f (closedBall c (5 / 4)))
    (hc : |c.im| ≤ H) (hs : 1 - δ ≤ s.re)
    (hfree : ∀ u : ℂ, 1 - 2 * δ ≤ u.re → |u.im| ≤ H + 2 → f u ≠ 0) :
    ‖∑ᶠ u, (divisor f (closedBall c (5 / 4)) u : ℂ) / (s - u)‖ ≤
      (((∑ᶠ u, divisor f (closedBall c (5 / 4)) u) : ℤ) : ℝ) / δ := by
  exact norm_divisor_zero_sum_le hf (isCompact_closedBall _ _) s δ hδ
    (divisor_zero_separation_of_zero_free_rectangle c s δ H hf hc hs hfree)

end TwinPrime.Analytic
