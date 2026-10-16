import Tengoku.NavierStokesEuler.Euler.PacketPhysicalNormBounds

/-!
Actual target amplification and the resulting exponential gain for
bounded history sizes and the packet amplitude chosen at target.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketGrowth InnerProductSpace

theorem equation30_target_exp_le {σ T Θ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hTtarget : 1/σ ≤ T) (hTΘ : T ≤ Θ)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    exp (1/(4*σ)) ≤ Θ*Z T := by
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hx : 1 ≤ σ*T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh]
  have hxpos : 0 < σ*T := by positivity
  have hgrowth := equation30_endpoint_exponential (sq_pos_of_pos hσ)
    (by nlinarith only [hσ, hσsmall] : σ^2 ≤ 1/16)
    (fun t ht => hZ t ht.1) (fun t ht => hfluxZ t ht.1) hZ0 hZ₁0
  rw [sqrt_sq hσ.le] at hgrowth
  have hpost := equation30_post_inversion_lower hσ hσsmall hZ hfluxZ hZ0 hZ₁0 (σ*T) hx
  rw [mul_div_cancel_left₀ T (ne_of_gt hσ)] at hpost
  have hraw : exp (1/(4*σ)) ≤ (σ*T)*Z T := by
    have hh := (div_le_iff₀ hxpos).mp hpost.1
    nlinarith only [hgrowth, hh]
  have hcoeff : σ*T ≤ Θ := by
    have hh := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith only [hσsmall]) hTpos.le
    nlinarith only [hh, hTΘ]
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hpost.2.le)

/-- A bounded physical history size, or the numerator used to choose a
packet amplitude, gains the actual target's exponential factor. -/
theorem ratio_bound_from_target_growth {s₀ Θ x target value bound : ℝ}
    (hs₀ : 0 < s₀) (hΘ : 0 < Θ) (hbound : 0 ≤ bound) (hvalue : value ≤ bound)
    (hgrowth : s₀*exp x ≤ 4*Θ*target) :
    0 < target ∧ value/target ≤ (4*Θ*bound/s₀)*exp (-x) := by
  have hleft : 0 < s₀*exp x := mul_pos hs₀ (exp_pos x)
  have htarget : 0 < target := by
    by_contra hn
    have hnon : target ≤ 0 := le_of_not_gt hn
    have hmul : 4*Θ*target ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hnon
    linarith only [hleft, hgrowth, hmul]
  have hexp : exp x*exp (-x) = 1 := by rw [← exp_add]; simp
  have hscaled : s₀ ≤ 4*Θ*target*exp (-x) := by
    have hh := mul_le_mul_of_nonneg_right hgrowth (exp_pos (-x)).le
    simpa only [mul_assoc, hexp, mul_one] using hh
  have hb : bound ≤ ((4*Θ*bound/s₀)*exp (-x))*target := by
    calc
      bound = (bound/s₀)*s₀ := by field_simp
      _ ≤ (bound/s₀)*(4*Θ*target*exp (-x)) :=
        mul_le_mul_of_nonneg_left hscaled (div_nonneg hbound hs₀.le)
      _ = _ := by ring
  exact ⟨htarget, (div_le_iff₀ htarget).mpr (hvalue.trans hb)⟩

end EulerPacketMovingFrame
