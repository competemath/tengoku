import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite additive exponential kernels

The geometric-series estimate bounds a unit-circle kernel both by its length
and by the reciprocal chord distance to one. Jordan's inequality converts the
chord distance into distance to the nearest integer for real frequencies.
All statements are finite and independent of any large-sieve hypothesis.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h2v.s5.91ebe3ae83d7 from=translated src=- shape=f2ece726 vocab=c9bd3bf8
-/
theorem norm_geom_sum_le_length {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ n ∈ range N, z ^ n‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ range N, ‖z ^ n‖ := norm_sum_le _ _
    _ = _ := by simp [norm_pow, hz]

/--
@isnad1 id=le.2h2v.s6.b95377d2a3c8 from=translated src=- shape=0880b179 vocab=b9bd7034
-/
theorem norm_geom_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (N : ℕ) :
    ‖∑ n ∈ range N, z ^ n‖ ≤ 2 / ‖1 - z‖ := by
  rw [geom_sum_eq hz1, norm_div]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by norm_num [norm_pow, hz]
  simpa only [norm_sub_rev] using
    div_le_div_of_nonneg_right hnum (norm_nonneg (z - 1))

/--
@isnad1 id=le.2h2v.s6.431ca356ee32 from=translated src=- shape=61723942 vocab=9477893c
-/
theorem norm_geom_sum_le_min {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (N : ℕ) :
    ‖∑ n ∈ range N, z ^ n‖ ≤ min (N : ℝ) (2 / ‖1 - z‖) :=
  le_min (norm_geom_sum_le_length hz N) (norm_geom_sum_le_two_div hz hz1 N)

/--
@isnad1 id=eq.1h3v.s6.0b0360e30cfb from=translated src=- shape=ea2c463e vocab=ec11e094
-/
theorem norm_shifted_geom_sum_eq {z : ℂ} (hz : ‖z‖ = 1) (M N : ℕ) :
    ‖∑ n ∈ range N, z ^ (M + n)‖ = ‖∑ n ∈ range N, z ^ n‖ := by
  simp only [pow_add, ← mul_sum, norm_mul, norm_pow, hz, one_pow, one_mul]

/--
@isnad1 id=le.1h3v.s6.e3eaf147e30f from=translated src=- shape=8c0da8ae vocab=7f34169d
-/
theorem norm_geom_sum_Ico_le_length {z : ℂ} (hz : ‖z‖ = 1) (M N : ℕ) :
    ‖∑ n ∈ Ico M N, z ^ n‖ ≤ (N - M : ℕ) := by
  calc
    _ ≤ ∑ n ∈ Ico M N, ‖z ^ n‖ := norm_sum_le _ _
    _ = _ := by simp [norm_pow, hz]

/--
@isnad1 id=le.2h3v.s6.51c1b2858cef from=translated src=- shape=486a2bb7 vocab=67415629
-/
theorem norm_geom_sum_Ico_le_min {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (M N : ℕ) :
    ‖∑ n ∈ Ico M N, z ^ n‖ ≤ min ((N - M : ℕ) : ℝ) (2 / ‖1 - z‖) := by
  apply le_min (norm_geom_sum_Ico_le_length hz M N)
  by_cases hMN : M ≤ N
  · rw [geom_sum_Ico hz1 hMN, norm_div]
    have hnum : ‖z ^ N - z ^ M‖ ≤ 2 := by
      calc
        _ ≤ ‖z ^ N‖ + ‖z ^ M‖ := norm_sub_le _ _
        _ = _ := by norm_num [norm_pow, hz]
    simpa only [norm_sub_rev] using
      div_le_div_of_nonneg_right hnum (norm_nonneg (z - 1))
  · rw [Ico_eq_empty (by omega), sum_empty, norm_zero]
    positivity

/-- The additive phase `exp(2πiθ)`, expressed through the unit circle.-/
def additivePhase (θ : ℝ) : ℂ := Circle.exp (2 * Real.pi * θ)

/--
@isnad1 id=eq.0h1v.s3.aa5a0e0f0df6 from=translated src=- shape=0cfb200e vocab=bf00cc6a
-/
@[simp] theorem norm_additivePhase (θ : ℝ) : ‖additivePhase θ‖ = 1 :=
  Circle.norm_coe _

/--
@isnad1 id=eq.0h1v.s5.143023c9f3f1 from=translated src=- shape=6d0eebef vocab=5c68fab1
-/
theorem additivePhase_eq_exp (θ : ℝ) :
    additivePhase θ = Complex.exp (2 * Real.pi * Complex.I * θ) := by
  unfold additivePhase
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring

/--
@isnad1 id=eq.0h2v.s5.41744f263517 from=translated src=- shape=e1908b7e vocab=4d692989
-/
theorem additivePhase_pow (θ : ℝ) (n : ℕ) :
    additivePhase θ ^ n = additivePhase (n * θ) := by
  unfold additivePhase
  rw [show (2 * Real.pi * ((n : ℝ) * θ)) = (n : ℝ) * (2 * Real.pi * θ) by ring,
    Circle.exp_natCast_mul, Circle.coe_pow]

/--
@isnad1 id=eq.0h2v.s4.8b640c53b60f from=translated src=- shape=00241260 vocab=46eb72ec
-/
theorem additivePhase_sub_int (θ : ℝ) (m : ℤ) :
    additivePhase (θ - m) = additivePhase θ := by
  unfold additivePhase
  rw [show 2 * Real.pi * (θ - m) = 2 * Real.pi * θ - m * (2 * Real.pi) by ring,
    Circle.exp_sub, Circle.exp_int_mul_two_pi, div_one]

/--
@isnad1 id=eq.0h2v.s5.49fcfec7dec1 from=translated src=- shape=1f3722c1 vocab=f9c92a86
-/
theorem additivePhase_sub (θ φ : ℝ) :
    additivePhase (θ - φ) = additivePhase θ * starRingEnd ℂ (additivePhase φ) := by
  unfold additivePhase
  rw [mul_sub, Circle.exp_sub, Circle.coe_div, div_eq_mul_inv,
    Complex.inv_eq_conj (Circle.norm_coe _)]

def additiveKernel (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ range N, additivePhase θ ^ n

/--
@isnad1 id=eq.0h2v.s6.c7ca10802247 from=translated src=- shape=e27fb3c1 vocab=c9d72087
-/
theorem additiveKernel_eq_sum_exp (N : ℕ) (θ : ℝ) :
    additiveKernel N θ =
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * θ)) := by
  unfold additiveKernel
  simp_rw [additivePhase_pow]
  simp only [additivePhase_eq_exp, Complex.ofReal_mul]

/--
@isnad1 id=le.0h2v.s4.d136a5d414b7 from=translated src=- shape=129bf7e1 vocab=3dfbdd7c
-/
theorem norm_additiveKernel_le_length (N : ℕ) (θ : ℝ) :
    ‖additiveKernel N θ‖ ≤ N := norm_geom_sum_le_length (norm_additivePhase θ) N

/-- The chord distance dominates four times the distance to the nearest integer.
@isnad1 id=le.0h1v.s6.cea5ba0b7ac5 from=translated src=- shape=15d62f21 vocab=21bb1996
-/
theorem four_mul_norm_unitAddCircle_le_chord (θ : ℝ) :
    4 * ‖(θ : UnitAddCircle)‖ ≤ ‖1 - additivePhase θ‖ := by
  let r : ℝ := θ - round θ
  have hr : |r| ≤ 1 / 2 := abs_sub_round θ
  have harg : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hsin' : 2 * |r| ≤ |Real.sin (Real.pi * r)| := by
    simpa only [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc,
      div_mul_cancel₀ _ Real.pi_ne_zero] using hsin
  have hchord : ‖1 - additivePhase r‖ = 2 * |Real.sin (Real.pi * r)| := by
    rw [norm_sub_rev, additivePhase_eq_exp]
    have heq : 2 * (Real.pi : ℂ) * Complex.I * r =
        Complex.I * ((2 * Real.pi * r : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * r) / 2 = Real.pi * r by ring]
    simp [Real.norm_eq_abs]
  rw [UnitAddCircle.norm_eq, ← additivePhase_sub_int θ (round θ)]
  change 4 * |r| ≤ ‖1 - additivePhase r‖
  rw [hchord]
  linarith

/--
@isnad1 id=le.1h2v.s8.53f79763a2e5 from=translated src=- shape=f74289cf vocab=de6f17a7
-/
theorem norm_additiveKernel_le_min (N : ℕ) (θ : ℝ)
    (hθ : (θ : UnitAddCircle) ≠ 0) :
    ‖additiveKernel N θ‖ ≤ min (N : ℝ) (1 / (2 * ‖(θ : UnitAddCircle)‖)) := by
  have hd : 0 < ‖(θ : UnitAddCircle)‖ := norm_pos_iff.mpr hθ
  have hchord := four_mul_norm_unitAddCircle_le_chord θ
  have hc : 0 < ‖1 - additivePhase θ‖ := by linarith
  have he : additivePhase θ ≠ 1 := by
    intro h
    simp [h] at hc
  apply le_min (norm_additiveKernel_le_length N θ)
  calc
    _ ≤ 2 / ‖1 - additivePhase θ‖ := norm_geom_sum_le_two_div (norm_additivePhase θ) he N
    _ ≤ 2 / (4 * ‖(θ : UnitAddCircle)‖) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hchord
    _ = _ := by ring

/--
@isnad1 id=le.2h3v.s6.0645f28284d8 from=translated src=- shape=14f1c1fe vocab=937ead97
-/
theorem norm_additiveKernel_le_of_separated (N : ℕ) (θ δ : ℝ) (hδ : 0 < δ)
    (hθ : δ ≤ ‖(θ : UnitAddCircle)‖) :
    ‖additiveKernel N θ‖ ≤ 1 / (2 * δ) := by
  have hθ0 : (θ : UnitAddCircle) ≠ 0 := norm_pos_iff.mp (hδ.trans_le hθ)
  exact ((norm_additiveKernel_le_min N θ hθ0).trans (min_le_right _ _)).trans
    (div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith))

/--
@isnad1 id=le.0h3v.s5.e16355385e28 from=translated src=- shape=fbbf9a6f vocab=50e52e80
-/
theorem norm_sum_Ico_additivePhase_le_length (M N : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Ico M N, additivePhase (n * θ)‖ ≤ (N - M : ℕ) := by
  simpa only [additivePhase_pow] using
    norm_geom_sum_Ico_le_length (norm_additivePhase θ) M N

/--
@isnad1 id=le.1h3v.s8.682da29cae04 from=translated src=- shape=bbf56e64 vocab=53eeedf2
-/
theorem norm_sum_Ico_additivePhase_le_min (M N : ℕ) (θ : ℝ)
    (hθ : (θ : UnitAddCircle) ≠ 0) :
    ‖∑ n ∈ Ico M N, additivePhase (n * θ)‖ ≤
      min ((N - M : ℕ) : ℝ) (1 / (2 * ‖(θ : UnitAddCircle)‖)) := by
  have hd : 0 < ‖(θ : UnitAddCircle)‖ := norm_pos_iff.mpr hθ
  have hchord := four_mul_norm_unitAddCircle_le_chord θ
  have hc : 0 < ‖1 - additivePhase θ‖ := by linarith
  have he : additivePhase θ ≠ 1 := by
    intro h
    simp [h] at hc
  have hk := norm_geom_sum_Ico_le_min (norm_additivePhase θ) he M N
  simp only [additivePhase_pow] at hk
  apply le_min (norm_sum_Ico_additivePhase_le_length M N θ)
  calc
    _ ≤ 2 / ‖1 - additivePhase θ‖ := hk.trans (min_le_right _ _)
    _ ≤ 2 / (4 * ‖(θ : UnitAddCircle)‖) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hchord
    _ = _ := by ring

/-- Exact correlation identity for two additive phases on a natural interval.
@isnad1 id=eq.0h4v.s6.4191aecb9d8b from=translated src=- shape=7a9a479b vocab=9c9b14ae
-/
theorem sum_Ico_phase_mul_conj_eq (M N : ℕ) (θ φ : ℝ) :
    (∑ n ∈ Ico M N, additivePhase (n * θ) *
      starRingEnd ℂ (additivePhase (n * φ))) =
      ∑ n ∈ Ico M N, additivePhase (n * (θ - φ)) := by
  apply sum_congr rfl
  intro n _
  rw [← additivePhase_sub]
  congr 1
  ring

/-- The off-diagonal Gram entry for frequencies separated on the unit circle.
@isnad1 id=le.2h5v.s8.929d71b86381 from=translated src=- shape=250571fb vocab=4341f2ef
-/
theorem norm_sum_Ico_phase_mul_conj_le (M N : ℕ) (θ φ δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ dist (θ : UnitAddCircle) (φ : UnitAddCircle)) :
    ‖∑ n ∈ Ico M N, additivePhase (n * θ) *
      starRingEnd ℂ (additivePhase (n * φ))‖ ≤
      min ((N - M : ℕ) : ℝ) (1 / (2 * δ)) := by
  have hnorm : δ ≤ ‖((θ - φ : ℝ) : UnitAddCircle)‖ := by
    simpa only [dist_eq_norm, ← QuotientAddGroup.mk_sub] using hsep
  have hne : ((θ - φ : ℝ) : UnitAddCircle) ≠ 0 := norm_pos_iff.mp (hδ.trans_le hnorm)
  rw [sum_Ico_phase_mul_conj_eq]
  apply (norm_sum_Ico_additivePhase_le_min M N (θ - φ) hne).trans
  exact min_le_min le_rfl
    (div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith))

end TwinPrime.Analytic
