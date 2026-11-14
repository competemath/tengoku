import Tengoku.Piirrationalitymeasure.Formalization.DiskContourDeformation
import Tengoku.Piirrationalitymeasure.Formalization.ComplexDensityModulus
import Tengoku.Piirrationalitymeasure.Formalization.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual integral and modulus formula for an arbitrary integer exponent triple. -/

namespace PiIrrationality

noncomputable def constructionParameter (a b c : ℕ) : ℝ × ℝ :=
  ((a : ℝ) / c, (b : ℝ) / c)

noncomputable def constructionDensity (a b c n : ℕ) (z : ℂ) : ℂ :=
  5 * z ^ (2 * a * n) * (z ^ 4 + 6 * z ^ 2 + 25) ^ (b * n) /
    (25 - z ^ 2) ^ (c * n + 1)

noncomputable def constructionIntegral (a b c n : ℕ) : ℂ :=
  -(∫ s : ℝ in (-2)..2, constructionDensity a b c n (verticalSegment s))

/--
@isnad1 id=eq.0h0v.s4.19f9b1826091 from=translated src=- shape=97937e61 vocab=18c13f29
-/
theorem constructionParameter_candidate : constructionParameter 1857 3714 5570 = candidate := by
  norm_num [constructionParameter, candidate]

/--
@isnad1 id=eq.0h1v.s4.94e1108166ff from=translated src=- shape=fe5e561e vocab=f80a53cd
-/
theorem constructionDensity_candidate (n : ℕ) :
    constructionDensity 1857 3714 5570 n = complexDensity n := rfl

/--
@isnad1 id=eq.0h1v.s4.3c1d2d7acf77 from=translated src=- shape=9932ec96 vocab=fa41be84
-/
theorem constructionIntegral_candidate (n : ℕ) :
    constructionIntegral 1857 3714 5570 n = paperIntegral n := rfl

/--
@isnad1 id=differen.1h5v.s6.5e241fa4abd4 from=translated src=- shape=97a5e0b6 vocab=b30b7cc9
-/
theorem constructionDensity_differentiableAt (a b c n : ℕ) {z : ℂ} (hz : ‖z‖ < 5) :
    DifferentiableAt ℂ (constructionDensity a b c n) z := by
  unfold constructionDensity
  fun_prop (disch := exact pow_ne_zero _ (complexDensity_den_ne_zero hz))

/--
@isnad1 id=eq.2h5v.s7.cd96a55b6976 from=translated src=- shape=9a9e557d vocab=508db825
-/
theorem constructionIntegral_deformed (a b c n : ℕ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    constructionIntegral a b c n = Complex.I *
      (-(∫ u in (0 : ℝ)..1,
          constructionDensity a b c n (smoothTauPlus e u) * deriv (smoothTauPlus e) u) +
        (∫ u in (0 : ℝ)..1,
          constructionDensity a b c n (smoothTauMinus e u) * deriv (smoothTauMinus e) u)) :=
  disk_density_deformation (fun _ hz => constructionDensity_differentiableAt a b c n hz) he0 he1

/--
@isnad1 id=eq.5h6v.s8.eb4891841cd7 from=translated src=- shape=63c7ca8d vocab=984d7140
-/
theorem constructionDensity_modulus (a b c n : ℕ) (hc : 0 < c) {z y : ℂ} (hy : z ^ 2 = y)
    (hy0 : y ≠ 0) (hq : y ^ 2 + 6 * y + 25 ≠ 0) (hp : 25 - y ≠ 0) :
    ‖constructionDensity a b c n z‖ = 5 / ‖25 - y‖ * Real.exp
      ((c : ℝ) * n * complexPhase ((a : ℝ) / c) ((b : ℝ) / c) y) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have he : (c : ℝ) * n * complexPhase ((a : ℝ) / c) ((b : ℝ) / c) y =
      ((a * n : ℕ) : ℝ) * Real.log ‖y‖ +
        ((b * n : ℕ) : ℝ) * Real.log ‖y ^ 2 + 6 * y + 25‖ -
          ((c * n : ℕ) : ℝ) * Real.log ‖25 - y‖ := by
    unfold complexPhase
    push_cast
    field_simp
  have hzpow : z ^ (2 * a * n) = y ^ (a * n) := by
    rw [← hy, ← pow_mul]
    congr 1
    ring
  have hzfour : z ^ 4 = y ^ 2 := by rw [← hy]; ring
  rw [constructionDensity, hzpow, hzfour, hy, norm_div, norm_mul, norm_mul, norm_pow,
    norm_pow, norm_pow, he, Real.exp_sub, Real.exp_add, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr hy0),
    Real.exp_log (norm_pos_iff.mpr hq), Real.exp_log (norm_pos_iff.mpr hp), pow_succ]
  norm_num only [Complex.norm_ofNat]
  field_simp
  rw [pow_succ]
  ring

/--
@isnad1 id=eq.0h5v.s6.9b13d0f33687 from=translated src=- shape=e2701f86 vocab=ceed796b
-/
theorem constructionDensity_conj (a b c n : ℕ) (z : ℂ) :
    constructionDensity a b c n (star z) = star (constructionDensity a b c n z) := by
  simp [constructionDensity]

/--
@isnad1 id=eq.2h5v.s5.2f2f4e87aafc from=translated src=- shape=b0cfe2b2 vocab=60b0b37e
-/
theorem constructionDensity_smoothTauPlus_one (a b c n : ℕ) (hb : 0 < b) (hn : 0 < n) (e : ℝ) :
    constructionDensity a b c n (smoothTauPlus e 1) = 0 := by
  rw [smoothTauPlus_at_one]
  have hz : (-1 - 2 * Complex.I : ℂ) ^ 4 + 6 * (-1 - 2 * Complex.I : ℂ) ^ 2 + 25 = 0 := by
    norm_num [Complex.ext_iff, pow_succ]
  simp only [constructionDensity, hz, zero_pow (Nat.mul_pos hb hn).ne', mul_zero, zero_div]

/--
@isnad1 id=eq.2h6v.s7.2925dc9eaa20 from=translated src=- shape=27eca7ab vocab=49351623
-/
theorem constructionDensity_lift_conj_norm (a b c n : ℕ) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    ‖constructionDensity a b c n (smoothTauMinus e u) * deriv (smoothTauMinus e) u‖ =
      ‖constructionDensity a b c n (smoothTauPlus e u) * deriv (smoothTauPlus e) u‖ := by
  rw [smoothTauPlus_deriv_conj he0 he1, smoothTauMinus, constructionDensity_conj, ← star_mul, norm_star]
  rw [mul_comm]

end PiIrrationality
