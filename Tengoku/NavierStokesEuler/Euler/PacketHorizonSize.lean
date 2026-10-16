import Tengoku.NavierStokesEuler.Euler.PacketBeforeTargetSize

/-!
The primary size remains controlled on the short interval after target.
The actual scalar ODE gives the needed uniform logarithmic growth bound;
there is no separate post-target growth hypothesis.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketGrowth EulerPacketFrameStability InnerProductSpace

theorem equation30_short_size_comparison {σ s t : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4)
    (hZ : ∀ x, 0 ≤ x → HasDerivAt Z (Z₁ x) x)
    (hfluxZ : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*Z₁ u)
      (2*(1-σ^2*(σ^2*x^2))*Z x) x)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t-s ≤ 1) :
    idealPrimarySize σ Z t ≤ 2*exp 6*idealPrimarySize σ Z s := by
  let W : ℝ → ℝ := fun x => (1+σ^2*x^2)*Z x
  let W₁ : ℝ → ℝ := fun x => (2*σ^2*x)*Z x+(1+σ^2*x^2)*Z₁ x
  have hzpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hW (x : ℝ) (hx : 0 ≤ x) : HasDerivAt W (W₁ x) x := by
    convert! (((((hasDerivAt_id x).pow 2).const_mul (σ^2)).const_add 1).mul (hZ x hx)) using 1
    dsimp [W₁]
    ring
  have hWpos (x : ℝ) (hx : 0 ≤ x) : 0 < W x := mul_pos (by positivity) (hzpos x hx)
  have hderivBound (x : ℝ) (hx : 1 ≤ x) : |W₁ x| ≤ 6*W x := by
    have hx0 : 0 ≤ x := by linarith only [hx]
    have hlog := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 x hx
    have hzx := hzpos x hx0
    rw [abs_div, abs_of_pos hzx, div_le_iff₀ hzx] at hlog
    have ht := abs_add_le ((2*σ^2*x)*Z x) ((1+σ^2*x^2)*Z₁ x)
    rw [abs_of_nonneg (by positivity : 0 ≤ (2*σ^2*x)*Z x), abs_mul,
      abs_of_pos (by positivity : 0 < 1+σ^2*x^2)] at ht
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1+σ^2*x^2 by positivity)
    have hx2 : x ≤ x^2 := by nlinarith only [hx]
    have hcoef := mul_le_mul_of_nonneg_right hx2 (show 0 ≤ 2*σ^2*Z x by positivity)
    dsimp [W₁, W]
    nlinarith only [ht, hh, hcoef, hzx]
  have hcont : ContinuousOn W (Icc s t) := fun x hx =>
    (hW x (by linarith only [hs, hx.1])).continuousAt.continuousWithinAt
  have hright : ∀ x ∈ Ico s t, HasDerivWithinAt W (W₁ x) (Ici x) x :=
    fun x hx => (hW x (by linarith only [hs, hx.1])).hasDerivWithinAt
  have hs0 : 0 ≤ s := by linarith only [hs]
  have ht0 : 0 ≤ t := hs0.trans hst
  have hbound : ∀ x ∈ Ico s t, ‖W₁ x‖ ≤ 6*‖W x‖+0 := by
    intro x hx
    have hx1 : 1 ≤ x := hs.trans hx.1
    simpa only [Real.norm_eq_abs, abs_of_pos (hWpos x (by linarith only [hx1])), add_zero]
      using hderivBound x hx1
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hright
    (show ‖W s‖ ≤ W s by rw [Real.norm_eq_abs, abs_of_pos (hWpos s hs0)]) hbound t ⟨hst, le_rfl⟩
  rw [gronwallBound_ε0, Real.norm_eq_abs, abs_of_pos (hWpos t ht0)] at hg
  have hexp : exp (6*(t-s)) ≤ exp 6 := exp_le_exp.mpr (by linarith only [hshort])
  have hgrowth : W t ≤ W s*exp 6 := hg.trans (mul_le_mul_of_nonneg_left hexp (hWpos s hs0).le)
  have htWeight := (quadratic_weight_sqrt (show 0 ≤ σ^2*t^2 by positivity)).1
  have hsWeight := (quadratic_weight_sqrt (show 0 ≤ σ^2*s^2 by positivity)).2
  have hleft := mul_le_mul_of_nonneg_right htWeight (hzpos t ht0).le
  have hright' := mul_le_mul_of_nonneg_right hsWeight (hzpos s hs0).le
  have hrightExp := mul_le_mul_of_nonneg_right hright' (exp_pos (6:ℝ)).le
  dsimp [W] at hgrowth
  dsimp [idealPrimarySize]
  nlinarith only [hleft, hgrowth, hrightExp]

theorem equation30_horizon_size_comparison {σ T H τ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4)
    (hZ : ∀ x, 0 ≤ x → HasDerivAt Z (Z₁ x) x)
    (hfluxZ : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*Z₁ u)
      (2*(1-σ^2*(σ^2*x^2))*Z x) x)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) (hT : 1 ≤ T) (hshort : H-T ≤ 1)
    (hτ : 0 ≤ τ) (hτH : τ ≤ H) :
    idealPrimarySize σ Z τ ≤ 2*exp 6*idealPrimarySize σ Z T := by
  by_cases hpre : τ ≤ T
  · have hbound := equation30_ideal_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hτ hpre
    have hpos : 0 ≤ idealPrimarySize σ Z T := mul_nonneg (sqrt_nonneg _)
      (equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 T (by linarith only [hT])).le
    have he : 1 ≤ exp (6:ℝ) := one_le_exp_iff.mpr (by norm_num)
    have hh := mul_le_mul_of_nonneg_right he hpos
    nlinarith only [hbound, hh]
  · exact equation30_short_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hT
      (le_of_not_ge hpre) (by linarith only [hshort, hτH])

end EulerPacketMovingFrame
