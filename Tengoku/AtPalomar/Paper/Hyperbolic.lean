module

public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Hyperbolic identities and pointwise inequalities

The pointwise analytic ingredients of arXiv:2604.11921v2, Sections 3 and 4.
All hyperbolic functions are the actual real functions from mathlib.
-/

namespace Paper

noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

@[simp]theorem sech_zero : sech 0 = 1 := by simp [sech]
@[simp]theorem sech_neg (x : ℝ) : sech (-x) = sech x := by simp [sech]

theorem sech_pos (x : ℝ) : 0 < sech x := one_div_pos.mpr (Real.cosh_pos x)

theorem sech_le_one (x : ℝ) : sech x ≤ 1 := by
  rw [sech, div_le_one (Real.cosh_pos x)]
  exact Real.one_le_cosh x

theorem sech_sq_pos (x : ℝ) : 0 < sech x ^ 2 := sq_pos_of_pos (sech_pos x)

theorem sech_sq_le_one (x : ℝ) : sech x ^ 2 ≤ 1 := by
  have hp := sech_pos x
  have hl := sech_le_one x
  nlinarith

theorem tanh_sq_add_sech_sq (x : ℝ) : Real.tanh x ^ 2 + sech x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  have h := Real.cosh_sq_sub_sinh_sq x
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith

theorem sech_fourth_pos (x : ℝ) : 0 < sech x ^ 4 := pow_pos (sech_pos x) 4

theorem sech_fourth_le_one (x : ℝ) : sech x ^ 4 ≤ 1 := by
  simpa using pow_le_pow_left₀ (sech_pos x).le (sech_le_one x) 4

theorem tanh_sq_lt_one (x : ℝ) : Real.tanh x ^ 2 < 1 := by
  have hi := tanh_sq_add_sech_sq x
  have hp := sech_sq_pos x
  nlinarith

theorem tanh_sq_le_one (x : ℝ) : Real.tanh x ^ 2 ≤ 1 := (tanh_sq_lt_one x).le

theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

theorem tanh_neg_of_neg {x : ℝ} (hx : x < 0) : Real.tanh x < 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr hx) (Real.cosh_pos x)

/-- A strict pointwise inequality underlying `B - T > 0` in Appendix Proposition 1.2.-/
theorem tanh_sub_mul_sech_sq_pos {y : ℝ} (hy : 0 < y) :
    0 < Real.tanh y - y * sech y ^ 2 := by
  have hs : 2 * y < Real.sinh (2 * y) := Real.self_lt_sinh_iff.mpr (by linarith)
  have hdouble : Real.sinh (2 * y) = 2 * Real.sinh y * Real.cosh y := by
    rw [two_mul, Real.sinh_add]
    ring
  rw [hdouble] at hs
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  have hc : Real.cosh y ≠ 0 := ne_of_gt (Real.cosh_pos y)
  have heq : Real.sinh y / Real.cosh y - y * (1 / Real.cosh y) ^ 2 =
      (Real.sinh y * Real.cosh y - y) / Real.cosh y ^ 2 := by
    field_simp
  rw [heq]
  exact div_pos (by nlinarith) (sq_pos_of_pos (Real.cosh_pos y))

theorem mul_tanh_pos {y : ℝ} (hy : y ≠ 0) : 0 < y * Real.tanh y := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · exact mul_pos_of_neg_of_neg hneg (tanh_neg_of_neg hneg)
  · exact mul_pos hpos (tanh_pos hpos)

/-- The scalar double-integrand in the paper's heat-kernel comparison is nonnegative.-/
theorem even_radial_comonotone {f g : ℝ → ℝ}
    (hf_even : ∀ x, f (-x) = f x) (hg_even : ∀ x, g (-x) = g x)
    (hf : AntitoneOn f (Set.Ici 0)) (hg : AntitoneOn g (Set.Ici 0))
    (x y : ℝ) : 0 ≤ (f x - f y) * (g x - g y) := by
  have habsf : ∀ z, f |z| = f z := by
    intro z
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_nonpos hz, hf_even]
  have habsg : ∀ z, g |z| = g z := by
    intro z
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_nonpos hz, hg_even]
  rcases le_total |x| |y| with hxy | hyx
  · have hfx := hf (abs_nonneg x) (abs_nonneg y) hxy
    have hgx := hg (abs_nonneg x) (abs_nonneg y) hxy
    rw [habsf, habsf] at hfx
    rw [habsg, habsg] at hgx
    exact mul_nonneg (sub_nonneg.mpr hfx) (sub_nonneg.mpr hgx)
  · have hfx := hf (abs_nonneg y) (abs_nonneg x) hyx
    have hgx := hg (abs_nonneg y) (abs_nonneg x) hyx
    rw [habsf, habsf] at hfx
    rw [habsg, habsg] at hgx
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfx) (sub_nonpos.mpr hgx)

theorem sech_antitoneOn : AntitoneOn sech (Set.Ici 0) := by
  intro x hx y hy hxy
  dsimp [sech]
  exact one_div_le_one_div_of_le (Real.cosh_pos x)
    (Real.cosh_strictMonoOn.monotoneOn hx hy hxy)

theorem sech_cube_antitoneOn : AntitoneOn (fun x => sech x ^ 3) (Set.Ici 0) := by
  intro x hx y hy hxy
  exact pow_le_pow_left₀ (sech_pos y).le (sech_antitoneOn hx hy hxy) 3

theorem sech_cube_comonotone {f : ℝ → ℝ}
    (hf_even : ∀ x, f (-x) = f x) (hf : AntitoneOn f (Set.Ici 0))
    (x y : ℝ) : 0 ≤ (f x - f y) * (sech x ^ 3 - sech y ^ 3) :=
  even_radial_comonotone hf_even (by intro z; simp) hf sech_cube_antitoneOn x y

/-- The Gaussian factor of the paper's even weight, with the positive normalizing
constant removed. The parameters are variance `v` and tilt `c = h / v`.-/
noncomputable def radialWeight (v c x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (2 * v)) * Real.cosh (c * x) / Real.cosh x

theorem radialWeight_pos (v c x : ℝ) : 0 < radialWeight v c x := by
  exact div_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _)) (Real.cosh_pos _)

@[simp]theorem radialWeight_neg (v c x : ℝ) :
    radialWeight v c (-x) = radialWeight v c x := by
  simp [radialWeight]

theorem cosh_generator_conjugation (x a b d : ℝ) :
    (Real.cosh x * a + 2 * Real.sinh x * b + Real.cosh x * d) /
        (2 * Real.cosh x) - a / 2 =
      d / 2 + Real.tanh x * b := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

end Paper
