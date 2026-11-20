import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace Erdos1133

def sixthLatticeWeight (k : ℤ) : ℝ := 1 / (1 + |(k : ℝ)|) ^ 6

theorem sixthLatticeWeight_nonneg (k : ℤ) : 0 ≤ sixthLatticeWeight k := by
  unfold sixthLatticeWeight
  positivity

theorem sixthLatticeWeight_summable : Summable sixthLatticeWeight := by
  have hnat : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 6 := by
    simpa using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (6 : ℕ)))
  apply Summable.of_nat_of_neg
  · simpa [sixthLatticeWeight, abs_of_nonneg, add_comm] using hnat
  · simpa [sixthLatticeWeight, abs_of_nonneg, add_comm] using hnat

/-- The parameter `T` is the actual period; the application takes `T=2N`.-/
def periodize (g : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℤ, g (z + ((T * (k : ℝ) : ℝ) : ℂ))

/-- A summable majorant on any bounded complex disk.-/
theorem periodize_term_local_bound (g : ℂ → ℂ) {C σ T R : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T) (hR : 0 ≤ R)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) (hz : ‖z‖ ≤ R) (k : ℤ) :
    ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ ≤
      (C * Real.exp (σ * R) * ((T + R + 1) / T) ^ 6) * sixthLatticeWeight k := by
  let u := z + ((T * (k : ℝ) : ℝ) : ℂ)
  have him : |u.im| ≤ R := by
    simpa [u] using (Complex.abs_im_le_norm z).trans hz
  have htri : T * |(k : ℝ)| ≤ ‖u‖ + R := by
    have ht := norm_sub_le u z
    have heq : u - z = ((T * (k : ℝ) : ℝ) : ℂ) := by dsimp [u]; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hT] at ht
    linarith
  have hden : T * (1 + |(k : ℝ)|) ≤ (T + R + 1) * (1 + ‖u‖) := by
    nlinarith [norm_nonneg u, mul_nonneg (add_nonneg hT.le hR) (norm_nonneg u)]
  have hr : (1 + |(k : ℝ)|) / (1 + ‖u‖) ≤ (T + R + 1) / T := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + ‖u‖) hT).2
    nlinarith
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |(k : ℝ)|) / (1 + ‖u‖)) hr 6
  have hexp : Real.exp (σ * |u.im|) ≤ Real.exp (σ * R) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left him hσ
  calc
    ‖g u‖ ≤ C * Real.exp (σ * |u.im|) / (1 + ‖u‖) ^ 6 := hg u
    _ ≤ C * Real.exp (σ * R) / (1 + ‖u‖) ^ 6 := by gcongr
    _ = (C * Real.exp (σ * R) *
        ((1 + |(k : ℝ)|) / (1 + ‖u‖)) ^ 6) * sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr6 (by positivity)) (sixthLatticeWeight_nonneg k)

theorem periodize_summable (g : ℂ → ℂ) {C σ T : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) : Summable fun k : ℤ => g (z + ((T * (k : ℝ) : ℝ) : ℂ)) := by
  apply Summable.of_norm_bounded
    (sixthLatticeWeight_summable.mul_left
      (C * Real.exp (σ * ‖z‖) * ((T + ‖z‖ + 1) / T) ^ 6))
  exact fun k => periodize_term_local_bound g hC hσ hT (norm_nonneg z) hg z le_rfl k

theorem differentiable_periodize (g : ℂ → ℂ) {C σ T : ℝ}
    (hd : Differentiable ℂ g) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6) :
    Differentiable ℂ (periodize g T) := by
  intro z
  let R := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs := sixthLatticeWeight_summable.mul_left
    (C * Real.exp (σ * R) * ((T + R + 1) / T) ^ 6)
  have hdiff : DifferentiableOn ℂ (periodize g T) (Metric.ball 0 R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hs
    · intro k
      exact (hd.comp (differentiable_id.add_const _)).differentiableOn
    · exact Metric.isOpen_ball
    · intro k w hw
      apply periodize_term_local_bound g hC hσ hT hR hg w
      exact le_of_lt (by simpa [Metric.mem_ball] using hw)
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by
    simp [Metric.mem_ball, R]))

theorem periodize_periodic (g : ℂ → ℂ) (T : ℝ) :
    Function.Periodic (periodize g T) (T : ℂ) := by
  intro z
  unfold periodize
  have he := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k : ℤ => g (z + ((T * (k : ℝ) : ℝ) : ℂ)))
  convert he using 1
  congr 1
  funext k
  congr 1
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  push_cast
  ring

theorem periodize_real (g : ℂ → ℂ) {C σ T : ℝ}
    (hreal : ∀ x : ℝ, (g x).im = 0) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (x : ℝ) : (periodize g T x).im = 0 := by
  have hs := periodize_summable g hC hσ hT hg (x : ℂ)
  change Complex.imCLM (∑' k : ℤ, g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))) = 0
  rw [Complex.imCLM.map_tsum hs]
  have he : ∀ k : ℤ, Complex.imCLM (g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))) = 0 := by
    intro k
    change (g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))).im = 0
    rw [← Complex.ofReal_add]
    exact hreal _
  simp_rw [he]
  simp

/-- A bound uniform in the height of a vertical strip, preserving the exact
exponential type.-/
theorem periodize_term_strip_bound (g : ℂ → ℂ) {C σ T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T) (hR : 0 ≤ R)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) (hz : |z.re| ≤ R) (k : ℤ) :
    ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ ≤
      (C * Real.exp (σ * |z.im|) * ((T + R + 1) / T) ^ 6) * sixthLatticeWeight k := by
  let u := z + ((T * (k : ℝ) : ℝ) : ℂ)
  have him : u.im = z.im := by simp [u]
  have htri : T * |(k : ℝ)| ≤ ‖u‖ + R := by
    have ht : |u.re - z.re| ≤ |u.re| + |z.re| := by
      simpa using abs_sub_le u.re 0 z.re
    have heq : u.re - z.re = T * (k : ℝ) := by simp [u]
    rw [heq, abs_mul, abs_of_pos hT] at ht
    linarith [Complex.abs_re_le_norm u]
  have hden : T * (1 + |(k : ℝ)|) ≤ (T + R + 1) * (1 + ‖u‖) := by
    nlinarith [norm_nonneg u, mul_nonneg (add_nonneg hT.le hR) (norm_nonneg u)]
  have hr : (1 + |(k : ℝ)|) / (1 + ‖u‖) ≤ (T + R + 1) / T := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + ‖u‖) hT).2
    nlinarith
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |(k : ℝ)|) / (1 + ‖u‖)) hr 6
  calc
    ‖g u‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖u‖) ^ 6 := by simpa [him] using hg u
    _ = (C * Real.exp (σ * |z.im|) *
        ((1 + |(k : ℝ)|) / (1 + ‖u‖)) ^ 6) * sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr6 (by positivity)) (sixthLatticeWeight_nonneg k)

theorem periodize_strip_bound (g : ℂ → ℂ) {C σ T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T) (hR : 0 ≤ R)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) (hz : |z.re| ≤ R) :
    ‖periodize g T z‖ ≤
      (C * ((T + R + 1) / T) ^ 6 * ∑' k : ℤ, sixthLatticeWeight k) * Real.exp (σ * |z.im|) := by
  let A := C * Real.exp (σ * |z.im|) * ((T + R + 1) / T) ^ 6
  have hmaj := sixthLatticeWeight_summable.mul_left A
  have hn : Summable fun k : ℤ => ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (periodize_term_strip_bound g hC hT hR hg z hz) hmaj
  calc
    ‖periodize g T z‖ ≤ ∑' k : ℤ, ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ, A * sixthLatticeWeight k :=
      Summable.tsum_le_tsum (periodize_term_strip_bound g hC hT hR hg z hz) hn hmaj
    _ = _ := by rw [tsum_mul_left]; dsimp [A]; ring

theorem periodize_term_tail_bound (g : ℂ → ℂ) {C σ T : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (x : ℝ) (hx : |x| ≤ T / 2) (k : ℤ) (hk : k ≠ 0) :
    ‖g ((x + T * (k : ℝ) : ℝ) : ℂ)‖ ≤
      (4096 * C / T ^ 6) * sixthLatticeWeight k := by
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hh : (0 : ℤ) < |k| := abs_pos.mpr hk
    exact_mod_cast (show (1 : ℤ) ≤ |k| by omega)
  have htri : T * |(k : ℝ)| ≤ |x + T * (k : ℝ)| + |x| := by
    have ht : |(x + T * (k : ℝ)) - x| ≤ |x + T * (k : ℝ)| + |x| := by
      simpa using abs_sub_le (x + T * (k : ℝ)) 0 x
    simpa [abs_mul, abs_of_pos hT] using ht
  have hden : T * (1 + |(k : ℝ)|) ≤ 4 * (1 + |x + T * (k : ℝ)|) := by
    nlinarith [mul_le_mul_of_nonneg_left hk1 hT.le]
  have hr : (1 + |(k : ℝ)|) / (1 + |x + T * (k : ℝ)|) ≤ 4 / T := by
    apply (div_le_div_iff₀ (by positivity) hT).2
    nlinarith
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤
    (1 + |(k : ℝ)|) / (1 + |x + T * (k : ℝ)|)) hr 6
  have hreal : ‖g ((x + T * (k : ℝ) : ℝ) : ℂ)‖ ≤ C / (1 + |x + T * (k : ℝ)|) ^ 6 := by
    simpa only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one,
      Complex.norm_real, Real.norm_eq_abs] using hg ((x + T * (k : ℝ) : ℝ) : ℂ)
  calc
    _ ≤ C / (1 + |x + T * (k : ℝ)|) ^ 6 := hreal
    _ = (C * ((1 + |(k : ℝ)|) / (1 + |x + T * (k : ℝ)|)) ^ 6) * sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ (C * (4 / T) ^ 6) * sixthLatticeWeight k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr6 hC) (sixthLatticeWeight_nonneg k)
    _ = _ := by ring

/-- Uniform error on the central period interval, sufficient to preserve peaks
and bounded labels when the period tends to infinity.-/
theorem periodize_real_error (g : ℂ → ℂ) {C σ T : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (x : ℝ) (hx : |x| ≤ T / 2) :
    ‖periodize g T x - g x‖ ≤
      (4096 * C / T ^ 6) * ∑' k : ℤ, sixthLatticeWeight k := by
  let r : ℤ → ℂ := fun k => if k = 0 then 0 else g ((x + T * (k : ℝ) : ℝ) : ℂ)
  have hbound : ∀ k : ℤ, ‖r k‖ ≤ (4096 * C / T ^ 6) * sixthLatticeWeight k := by
    intro k
    by_cases hk : k = 0
    · simp only [r, hk, ite_eq_left rfl, norm_zero]
      exact mul_nonneg (by positivity) (sixthLatticeWeight_nonneg 0)
    · simpa [r, hk] using periodize_term_tail_bound g hC hT hg x hx k hk
  have hmaj := sixthLatticeWeight_summable.mul_left (4096 * C / T ^ 6)
  have hn : Summable fun k : ℤ => ‖r k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound hmaj
  have hsum : periodize g T x - g x = ∑' k : ℤ, r k := by
    have heq := (periodize_summable g hC hσ hT hg (x : ℂ)).tsum_eq_add_tsum_ite 0
    simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero, add_zero] at heq
    have hre : (fun k : ℤ => if k = 0 then 0 else g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))) = r := by
      funext k
      simp [r]
    rw [hre] at heq
    exact eq_sub_iff_add_eq.mpr (by simpa [periodize, add_comm] using heq.symm) |>.symm
  rw [hsum]
  calc
    ‖∑' k : ℤ, r k‖ ≤ ∑' k : ℤ, ‖r k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ, (4096 * C / T ^ 6) * sixthLatticeWeight k :=
      Summable.tsum_le_tsum hbound hn hmaj
    _ = _ := tsum_mul_left

/-- Vertical contour translation for an entire periodic function: the two
vertical sides cancel exactly.-/
theorem periodic_horizontal_integral (H : ℂ → ℂ) {T : ℝ}
    (hd : Differentiable ℂ H) (hp : Function.Periodic H (T : ℂ)) (y : ℝ) :
    (∫ x : ℝ in (-T / 2)..(T / 2), H (x : ℂ)) =
      ∫ x : ℝ in (-T / 2)..(T / 2), H ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hv : ∀ t : ℝ, H (((T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      H (((-T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have heq : (((T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (((-T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + (T : ℂ) := by push_cast; ring
    rw [heq, hp]
  have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H
    (((-T / 2 : ℝ) : ℂ)) (((T / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) hd.differentiableOn
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_mul, sub_zero, add_zero, zero_add, Complex.ofReal_zero] at hr
  simp_rw [hv] at hr
  have hr' : (∫ x : ℝ in (-T / 2)..(T / 2), H (x : ℂ)) -
      (∫ x : ℝ in (-T / 2)..(T / 2), H ((x : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    simpa only [add_sub_cancel_right] using hr
  exact sub_eq_zero.mp hr'

def frequencyTwist (H : ℂ → ℂ) (T : ℝ) (j : ℤ) (z : ℂ) : ℂ :=
  H z * Complex.exp (-(2 * Real.pi * (j : ℝ) / T : ℝ) * Complex.I * z)

theorem differentiable_frequencyTwist (H : ℂ → ℂ) (T : ℝ) (j : ℤ)
    (hd : Differentiable ℂ H) : Differentiable ℂ (frequencyTwist H T j) := by
  exact hd.mul (Complex.differentiable_exp.comp (differentiable_id.const_mul _))

theorem frequencyTwist_periodic (H : ℂ → ℂ) {T : ℝ} (hT : T ≠ 0)
    (hp : Function.Periodic H (T : ℂ)) (j : ℤ) :
    Function.Periodic (frequencyTwist H T j) (T : ℂ) := by
  intro z
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  unfold frequencyTwist
  rw [hp]
  have heq : (-(2 * Real.pi * (j : ℝ) / T : ℝ) : ℂ) * Complex.I * (z + (T : ℂ)) =
      (-(2 * Real.pi * (j : ℝ) / T : ℝ) : ℂ) * Complex.I * z +
        ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp [hTc]
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_frequencyTwist (H : ℂ → ℂ) (T : ℝ) (j : ℤ) (z : ℂ) :
    ‖frequencyTwist H T j z‖ =
      ‖H z‖ * Real.exp ((2 * Real.pi * (j : ℝ) / T) * z.im) := by
  rw [frequencyTwist, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

/-- Entire periodic functions of exponential type have no Fourier modes above
that type. This is proved by an actual Cauchy contour translation.-/
theorem frequency_integral_eq_zero (H : ℂ → ℂ) {T K σ : ℝ}
    (hT : 0 < T) (_hK : 0 ≤ K) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ))
    (hbound : ∀ z : ℂ, |z.re| ≤ T / 2 → ‖H z‖ ≤ K * Real.exp (σ * |z.im|))
    (j : ℤ) (hfreq : σ < |2 * Real.pi * (j : ℝ) / T|) :
    (∫ x : ℝ in (-T / 2)..(T / 2), frequencyTwist H T j (x : ℂ)) = 0 := by
  let ω : ℝ := 2 * Real.pi * (j : ℝ) / T
  have ht : Tendsto (fun t : ℝ => K * T * Real.exp ((σ - |ω|) * t)) atTop (𝓝 0) := by
    have hneg : σ - |ω| < 0 := by dsimp [ω]; linarith
    simpa using (Real.tendsto_exp_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop_of_neg hneg)).const_mul (K * T)
  have hdecay : ∀ t : ℝ, 0 ≤ t →
      ‖∫ x : ℝ in (-T / 2)..(T / 2), frequencyTwist H T j (x : ℂ)‖ ≤
        K * T * Real.exp ((σ - |ω|) * t) := by
    intro t ht0
    let y : ℝ := if 0 ≤ ω then -t else t
    have hy : |y| = t := by
      dsimp [y]
      split_ifs <;> simp [abs_of_nonneg ht0]
    have hωy : ω * y = -|ω| * t := by
      dsimp [y]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h), neg_neg]
    rw [periodic_horizontal_integral (frequencyTwist H T j)
      (differentiable_frequencyTwist H T j hd) (frequencyTwist_periodic H hT.ne' hp j) y]
    have hib := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T / 2) (b := T / 2) (C := K * Real.exp ((σ - |ω|) * t))
      (f := fun x : ℝ => frequencyTwist H T j ((x : ℂ) + (y : ℂ) * Complex.I)) (by
        intro x hx
        have hx' : |x| ≤ T / 2 := by
          rw [uIoc_of_le (by linarith : -T / 2 ≤ T / 2)] at hx
          exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
        have hh := hbound ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hx')
        rw [norm_frequencyTwist]
        have him : (((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
        rw [him] at hh ⊢
        calc
          ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ * Real.exp (ω * y) ≤
              (K * Real.exp (σ * |y|)) * Real.exp (ω * y) :=
            mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
          _ = K * Real.exp ((σ - |ω|) * t) := by
            rw [mul_assoc, ← Real.exp_add, hy, hωy]
            congr 2
            ring)
    have hab : |T / 2 - (-T / 2)| = T := by rw [abs_of_nonneg (by linarith)]; ring
    rw [hab] at hib
    nlinarith
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact ge_of_tendsto ht (eventually_ge_atTop 0 |>.mono fun t ht => hdecay t ht)

def entirePeriodicCircle (H : ℂ → ℂ) (T : ℝ) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ)) : C(AddCircle T, ℂ) := by
  let hpR : Function.Periodic (fun x : ℝ => H (x : ℂ)) T := by
    intro x
    simpa only [Complex.ofReal_add] using hp (x : ℂ)
  exact ⟨hpR.lift, continuous_coinduced_dom.mpr (hd.continuous.comp Complex.continuous_ofReal)⟩

@[simp] theorem entirePeriodicCircle_apply (H : ℂ → ℂ) (T : ℝ)
    (hd : Differentiable ℂ H) (hp : Function.Periodic H (T : ℂ)) (x : ℝ) :
    entirePeriodicCircle H T hd hp (x : AddCircle T) = H (x : ℂ) := by
  rfl

theorem entirePeriodicCircle_coeff_eq_integral (H : ℂ → ℂ) (T : ℝ)
    [Fact (0 < T)] (hd : Differentiable ℂ H) (hp : Function.Periodic H (T : ℂ)) (j : ℤ) :
    fourierCoeff (entirePeriodicCircle H T hd hp) j =
      (1 / T : ℝ) • ∫ x : ℝ in (-T / 2)..(T / 2), frequencyTwist H T j (x : ℂ) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-T / 2), show -T / 2 + T = T / 2 by ring]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [fourier_coe_apply, entirePeriodicCircle_apply, smul_eq_mul]
  unfold frequencyTwist
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

theorem entirePeriodicCircle_coeff_zero (H : ℂ → ℂ) {T K σ : ℝ}
    [hT : Fact (0 < T)] (hK : 0 ≤ K) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ))
    (hbound : ∀ z : ℂ, |z.re| ≤ T / 2 → ‖H z‖ ≤ K * Real.exp (σ * |z.im|))
    (j : ℤ) (hfreq : σ < |2 * Real.pi * (j : ℝ) / T|) :
    fourierCoeff (entirePeriodicCircle H T hd hp) j = 0 := by
  rw [entirePeriodicCircle_coeff_eq_integral,
    frequency_integral_eq_zero H hT.out hK hd hp hbound j hfreq, smul_zero]

def periodizationBandwidth (σ T : ℝ) : ℕ := Nat.ceil (σ * T / (2 * Real.pi))

theorem periodizationBandwidth_le {σ T : ℝ} {n : ℕ}
    (h : σ * T / (2 * Real.pi) ≤ (n : ℝ)) :
    periodizationBandwidth σ T ≤ n := by
  exact Nat.ceil_le.mpr h

theorem frequency_above_band {σ T : ℝ} (hT : 0 < T) (j : ℤ)
    (hj : j ∉ Finset.Icc (-(periodizationBandwidth σ T : ℤ)) (periodizationBandwidth σ T : ℤ)) :
    σ < |2 * Real.pi * (j : ℝ) / T| := by
  have hn : ¬ |j| ≤ (periodizationBandwidth σ T : ℤ) := by
    intro h
    exact hj (Finset.mem_Icc.mpr (abs_le.mp h))
  have hjr : (periodizationBandwidth σ T : ℝ) < |(j : ℝ)| := by
    exact_mod_cast lt_of_not_ge hn
  have hceil : σ * T / (2 * Real.pi) ≤ (periodizationBandwidth σ T : ℝ) := Nat.le_ceil _
  have hratio := hceil.trans_lt hjr
  have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hratio
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos, abs_of_pos hT]
  exact (lt_div_iff₀ hT).mpr (by nlinarith)

/-- An actual finite Fourier expansion, rather than a bandwidth assumption.-/
theorem entire_periodic_finite_expansion (H : ℂ → ℂ) {T K σ : ℝ}
    [hT : Fact (0 < T)] (hK : 0 ≤ K) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ))
    (hbound : ∀ z : ℂ, |z.re| ≤ T / 2 → ‖H z‖ ≤ K * Real.exp (σ * |z.im|)) :
    ∃ c : ℤ → ℂ, ∀ x : ℝ,
      H (x : ℂ) = ∑ j ∈ Finset.Icc (-(periodizationBandwidth σ T : ℤ))
        (periodizationBandwidth σ T : ℤ),
          c j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (x : ℂ) / (T : ℂ)) := by
  classical
  let F := entirePeriodicCircle H T hd hp
  let s := Finset.Icc (-(periodizationBandwidth σ T : ℤ)) (periodizationBandwidth σ T : ℤ)
  have hz : ∀ j ∉ s, fourierCoeff F j = 0 := by
    intro j hj
    exact entirePeriodicCircle_coeff_zero H hK hd hp hbound j (frequency_above_band hT.out j hj)
  have hs : Summable (fourierCoeff F) := summable_of_ne_finset_zero hz
  refine ⟨fourierCoeff F, ?_⟩
  intro x
  have heq := (has_pointwise_sum_fourier_series_of_summable hs (x : AddCircle T)).tsum_eq
  rw [tsum_eq_sum (s := s) (by
    intro j hj
    rw [hz j hj, zero_smul])] at heq
  simpa [F, s, smul_eq_mul, fourier_coe_apply] using heq.symm

theorem periodize_finite_expansion (g : ℂ → ℂ) {C σ T : ℝ}
    [hT : Fact (0 < T)] (hd : Differentiable ℂ g) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6) :
    ∃ c : ℤ → ℂ, ∀ x : ℝ,
      periodize g T (x : ℂ) = ∑ j ∈ Finset.Icc (-(periodizationBandwidth σ T : ℤ))
        (periodizationBandwidth σ T : ℤ),
          c j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (x : ℂ) / (T : ℂ)) := by
  apply entire_periodic_finite_expansion (periodize g T)
    (K := C * ((T + T / 2 + 1) / T) ^ 6 * ∑' k : ℤ, sixthLatticeWeight k)
  · exact mul_nonneg (by positivity) (tsum_nonneg sixthLatticeWeight_nonneg)
  · exact differentiable_periodize g hd hC hσ hT.out hg
  · exact periodize_periodic g T
  · exact fun z hz => periodize_strip_bound g hC hT.out (by linarith [hT.out]) hg z hz

end Erdos1133
