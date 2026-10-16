import Tengoku.NavierStokesEuler.Euler.PacketActualFrameEstimates

/-!
The pressure numerator of the actual primary is positive.  The scale
condition `1 ≤ σ * Θ` is the source horizon condition; the smallness of the
matrix and ray errors is converted to smallness relative to `σ^2`.
-/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketGrowth EulerPacketFrameStability
  EulerPacketFrameQuantitative InnerProductSpace

theorem controlled_pressure_ratio_lower
    {A : Fin 3 → Fin 3 → ℝ} {σ Θ K e τ P Q N r : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hσΘ : 1 ≤ σ*Θ) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ) (hsmall : 1000000*K*e*Θ^40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |P-σ^2*τ^2| ≤ 800*e*Θ^5)
    (hQ : |Q-(-2*σ^2*τ)| ≤ 800*e*Θ^5)
    (hN : |N-1| ≤ 800*e*Θ^5)
    (hratio : |r+Z₁ τ/Z τ| ≤ 10*(K*e*Θ^29))
    (hA : ∀ i j, |A i j-idealVelocityEntry (σ^2) i j| ≤ 3*e) :
    σ^2/2 ≤ velocityNumerator A P Q N r 1 (velocityThird P Q N r 1) := by
  let ρ := 800*e*Θ^5
  let η := K*e*Θ^29
  let j := 147*e*Θ^4+1600*e*Θ^5
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hΘpos : 0 < Θ := by linarith only [hΘ]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hρ : ρ ≤ 1/2 := by
    have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)
    dsimp [ρ]
    nlinarith only [hp, hsmall]
  have hη : η ≤ 1/2 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))
      (mul_nonneg hK0 he)
    dsimp [η]
    nlinarith only [hp, hsmall]
  have ht2 : τ^2 ≤ Θ^2 := (sq_le_sq₀ hτ0 hΘ0).mpr hτΘ
  have hP₀ : |σ^2*τ^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    nlinarith only [mul_le_mul_of_nonneg_right hσ2 (sq_nonneg τ), ht2]
  have hQ₀ : |-2*σ^2*τ| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg hτ0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσ2 hτ0, hτΘ, hΘ, sq_nonneg (Θ-1)]
  obtain ⟨_, hp, hq, hn, hw, _, _⟩ := ray_geometric_bounds (ε := 0) (U := r) (V := 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hβ : |σ^2| ≤ 1 := by simpa only [abs_of_nonneg (sq_nonneg σ)] using hσ2
  have hJ : |velocityNumerator A P Q N r 1 (velocityThird P Q N r 1)-
      ((σ^2*τ^2+σ^2)*1+(-2*σ^2*τ)*r)| ≤ j*(|r|+|1|) := by
    have hh := velocity_numerator_error hΘ hρ0 (show 0 ≤ 3*e by positivity)
      hβ hA hp hq hn hP hQ hN hw
    dsimp [j, ρ] at *
    nlinarith only [hh]
  have hslope := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ
  have hr₀ : |-Z₁ τ/Z τ| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |r/1-(-Z₁ τ/Z τ)| ≤ 10*η := by
    simpa only [div_one, neg_div, sub_neg_eq_add] using hratio
  have herr := pressure_ratio_error hΘ hη0 hη hj (by norm_num : (0:ℝ) < 1) hQ₀ hr₀ hr' hJ
  simp only [div_one] at herr
  have herrorSmall : 10*j+20*Θ^2*η ≤ σ^2/2 := by
    have hp6 := scaled_power_le hΘ hK he (by decide : 6 ≤ 40)
    have hp7 := scaled_power_le hΘ hK he (by decide : 7 ≤ 40)
    have hp33 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 33 ≤ 40))
      (mul_nonneg hK0 he)
    have hs : (10*j+20*Θ^2*η)*Θ^2 ≤ 1/2 := by
      dsimp [j, η]
      nlinarith only [hp6, hp7, hp33, hsmall]
    have hστ : 1 ≤ σ^2*Θ^2 := by
      have hh := mul_le_mul hσΘ hσΘ (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ σ*Θ)
      nlinarith only [hh]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hΘpos)).mp
    nlinarith only [hs, hστ]
  have hZpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hnum := equation30_ideal_numerator_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hideal : σ^2 ≤ σ^2*τ^2+σ^2+(-2*σ^2*τ)*(-Z₁ τ/Z τ) := by
    apply (mul_le_mul_iff_right₀ hZpos).mp
    have hz : Z τ ≠ 0 := ne_of_gt hZpos
    have hid : (σ^2*τ^2+σ^2+(-2*σ^2*τ)*(-Z₁ τ/Z τ))*Z τ =
        (σ^2*τ^2+σ^2)*Z τ+2*σ^2*τ*Z₁ τ := by field_simp
    nlinarith only [hid, hnum]
  linarith only [(abs_le.mp herr).1, herrorSmall, hideal]

end EulerPacketMovingFrame
