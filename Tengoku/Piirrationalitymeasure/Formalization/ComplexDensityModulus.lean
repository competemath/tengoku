import Tengoku.Piirrationalitymeasure.Formalization.ContourDeformation
import Tengoku.Piirrationalitymeasure.Formalization.ArcPhase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual modulus identity (4.26) and conjugacy of the lifted integrands. -/

namespace PiIrrationality

theorem complexDensity_modulus (n : ℕ) {z y : ℂ} (hy : z ^ 2 = y)
    (hy0 : y ≠ 0) (hq : y ^ 2 + 6 * y + 25 ≠ 0) (hp : 25 - y ≠ 0) :
    ‖complexDensity n z‖ = 5 / ‖25 - y‖ * Real.exp
      (5570 * (n : ℝ) * complexPhase (1857 / 5570) (3714 / 5570) y) := by
  have he : 5570 * (n : ℝ) * complexPhase (1857 / 5570) (3714 / 5570) y =
      ((1857 * n : ℕ) : ℝ) * Real.log ‖y‖ +
        ((3714 * n : ℕ) : ℝ) * Real.log ‖y ^ 2 + 6 * y + 25‖ -
          ((5570 * n : ℕ) : ℝ) * Real.log ‖25 - y‖ := by
    unfold complexPhase
    push_cast
    ring
  have hzpow : z ^ (2 * 1857 * n) = y ^ (1857 * n) := by
    rw [← hy, ← pow_mul]
    congr 1
    omega
  have hzfour : z ^ 4 = y ^ 2 := by rw [← hy]; ring
  rw [complexDensity, hzpow, hzfour, hy, norm_div, norm_mul, norm_mul, norm_pow,
    norm_pow, norm_pow, he, Real.exp_sub, Real.exp_add, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr hy0),
    Real.exp_log (norm_pos_iff.mpr hq), Real.exp_log (norm_pos_iff.mpr hp), pow_succ]
  norm_num only [Complex.norm_ofNat]
  field_simp
  rw [pow_succ]
  ring

theorem complexDensity_conj (n : ℕ) (z : ℂ) :
    complexDensity n (star z) = star (complexDensity n z) := by
  simp [complexDensity]

theorem smoothTauPlus_deriv_conj {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    deriv (smoothTauMinus e) u = star (deriv (smoothTauPlus e) u) := by
  have h := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt u
    (((smoothTauPlus_contDiff he0 he1).differentiable (by norm_num) u).hasDerivAt)
  exact h.deriv

theorem smoothTauMinus_density_conj (n : ℕ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    complexDensity n (smoothTauMinus e u) * deriv (smoothTauMinus e) u =
      star (complexDensity n (smoothTauPlus e u) * deriv (smoothTauPlus e) u) := by
  rw [smoothTauPlus_deriv_conj he0 he1, smoothTauMinus, complexDensity_conj, star_mul]
  ring

theorem smoothTauMinus_density_norm (n : ℕ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    ‖complexDensity n (smoothTauMinus e u) * deriv (smoothTauMinus e) u‖ =
      ‖complexDensity n (smoothTauPlus e u) * deriv (smoothTauPlus e) u‖ := by
  rw [smoothTauMinus_density_conj n he0 he1, norm_star]

theorem complexDensity_zero (n : ℕ) (hn : 0 < n) : complexDensity n 0 = 0 := by
  simp [complexDensity, show 2 * 1857 * n ≠ 0 by omega]

theorem complexDensity_smoothTauPlus_one (n : ℕ) (hn : 0 < n) (e : ℝ) :
    complexDensity n (smoothTauPlus e 1) = 0 := by
  rw [smoothTauPlus_at_one]
  have hz : (-1 - 2 * Complex.I : ℂ) ^ 4 + 6 * (-1 - 2 * Complex.I : ℂ) ^ 2 + 25 = 0 := by
    norm_num [Complex.ext_iff, pow_succ]
  simp only [complexDensity, hz, zero_pow (show 3714 * n ≠ 0 by omega), mul_zero, zero_div]

theorem gammaPath_pole_norm_ge_twenty {e t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    20 ≤ ‖25 - gammaPath e t‖ := by
  have h := norm_le_norm_sub_add (25 : ℂ) (gammaPath e t)
  norm_num only [Complex.norm_ofNat] at h
  linarith [gammaPath_norm_le_five (eta := e) ht0 ht1]

theorem gammaPath_quadratic_ne_zero {e t : ℝ} (he : (9 : ℝ) / 10 < e)
    (ht0 : 0 < t) (ht1 : t < 1) : (gammaPath e t) ^ 2 + 6 * gammaPath e t + 25 ≠ 0 := by
  have h := arc_quadratic_normSq e t
  have hp : 0 < (1 - t) ^ 2 * arcH e t / arcD e t ^ 2 := by
    exact div_pos (mul_pos (sq_pos_of_pos (by linarith)) (arcH_pos he ht0.le ht1.le))
      (sq_pos_of_pos (arcD_pos e t))
  rw [← h] at hp
  exact Complex.normSq_pos.mp hp

end PiIrrationality
