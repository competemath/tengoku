import Tengoku.Piirrationalitymeasure.Formalization.CoefficientAsymptotic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordinary logarithmic growth of the actual coefficient in (4.11). -/

namespace PiIrrationality

open Filter PowerSeries
open scoped Topology

theorem sqrt_scaled_log_limit {p : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hp : ∀ᶠ n in atTop, 0 < p n)
    (h : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * p n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog := (h.log hL.ne').div_atTop tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => Real.log (Real.sqrt (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
    have ht := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).div_const 2
    convert! ht using 1
    · ext n
      rw [Real.log_sqrt (Nat.cast_nonneg n)]
      dsimp only [Function.comp_def, id_eq]
      ring
    · norm_num
  have hd := hlog.sub hs
  rw [sub_self] at hd
  apply hd.congr'
  filter_upwards [hp, eventually_gt_atTop (0 : ℕ)] with n hpn hn
  rw [Real.log_mul (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne' hpn.ne']
  ring

theorem Sseries_diagonal_log_formula {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.log (↑(coeff (q * n) (Sseries ^ n)) : ℝ) / (n : ℝ) =
      Real.log (SReal x) - q * Real.log x +
        Real.log (coefficientProbability x n (q * n)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [coefficientLaw_extraction hx0 hx1, coefficientLaw_toReal,
    Real.log_mul (div_ne_zero (pow_ne_zero _ (SReal_ne_zero hx0.le hx1))
      (pow_ne_zero _ hx0.ne')) (coefficientProbability_pos hx0 hx1 hn _).ne',
    Real.log_div (pow_ne_zero _ (SReal_ne_zero hx0.le hx1)) (pow_ne_zero _ hx0.ne'),
    Real.log_pow, Real.log_pow, Nat.cast_mul]
  field_simp

noncomputable def coefficientGrowthRate : ℝ :=
  (Real.log 25 + 3716 * Real.log 2 + Real.log (SReal coefficientSaddle) -
    5570 * Real.log coefficientSaddle) / 5570

theorem paper_pi_coeff_log_formula (n : ℕ) :
    Real.log |(↑(-laurentCoeffRat n 0 / 2) : ℝ)| =
      (n : ℝ) * (Real.log 25 + 3716 * Real.log 2) - Real.log 4 +
        Real.log (↑(coeff (5570 * n) (Sseries ^ n)) : ℝ) := by
  have he := congrArg (fun z : ℚ => (z : ℝ)) (paper_pi_coeff_extraction n)
  push_cast at he
  push_cast
  rw [he, Real.log_mul (by positivity)
    (show (↑(coeff (5570 * n) (Sseries ^ n)) : ℝ) ≠ 0 by
      exact_mod_cast (Sseries_diagonal_coeff_pos n).ne'),
    Real.log_div (by positivity) (by norm_num), Real.log_pow,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  norm_num

end PiIrrationality
