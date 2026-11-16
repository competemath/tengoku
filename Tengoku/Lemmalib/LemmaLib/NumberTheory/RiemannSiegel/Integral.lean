/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Tengoku.Lemmalib.LemmaLib.Analysis.Complex.RiemannSiegelLine
public import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Riemann–Siegel integral

This file defines the Riemann–Siegel integral
`R(s, c) = ∫_{c ↙} u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu}) du`
along the Riemann–Siegel line `u = c - ω x` (`x : ℝ`, `ω = exp (π i / 4)`) through a positive
non-integer real point `c`, and establishes its basic properties:

* `RiemannSiegel.norm_integrand_le`: a Gaussian bound `‖u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu})‖ ≤
  K exp (-π (Im u)²)` on the closed strip `c ≤ Re u - Im u ≤ c'`, uniform in `s` on bounded sets;
* `RiemannSiegel.integrable_integrand_line`: integrability along the lines;
* `RiemannSiegel.differentiable_rsIntegral`: `s ↦ R(s, c)` is entire;
* `RiemannSiegel.rsIntegral_eq_sub_of_lt`: moving the line from `c ∈ (n - 1, n)` to
  `c' ∈ (n, n + 1)` across the pole at `u = n` subtracts `n^{-s}`, so that
  `R(s, N + 1/2) = R(s, 1/2) - ∑_{n=1}^N n^{-s}` (`rsIntegral_add_half`).

The value `R(s, 1/2)` is the function `R_{0,0}(s)` of the Riemann–Siegel formula
`ζ(s) = R(s) + χ(s) conj (R (conj (1 - s)))` (Polymath (5.3) and Titchmarsh (2.10.6)), proved in
`LemmaLib.NumberTheory.RiemannSiegel.Formula`.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-- The Riemann–Siegel kernel `e^{iπu²} / (e^{iπu} - e^{-iπu})`.-/
@[expose] noncomputable def kernel (u : ℂ) : ℂ :=
  cexp (π * I * u ^ 2) / (cexp (π * I * u) - cexp (-(π * I * u)))

/--
@isnad1 id=eq.0h1v.s4.89b3b527abcb from=translated src=- shape=c1db08e2 vocab=89d28a00
-/
theorem kernel_eq_mordellIntegrand (u : ℂ) : kernel u = mordellIntegrand 1 0 u := by
  unfold kernel mordellIntegrand mordellExponent; simp

/-- The Riemann–Siegel integrand `u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu})`.-/
@[expose] noncomputable def integrand (s u : ℂ) : ℂ := u ^ (-s) * kernel u

/-- The Riemann–Siegel integral `∫_{c ↙} u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu}) du` along the
line `u = c - ω x` through the real point `c`.-/
@[expose] noncomputable def rsIntegral (s : ℂ) (c : ℝ) : ℂ :=
  ∫ x : ℝ, -ω * integrand s (c - ω * x)

/--
@isnad1 id=eq.0h2v.s6.ed15e03f7a20 from=translated src=- shape=61ffac5f vocab=2dc372cd
-/
theorem integrand_eq_gauss_mul (s u : ℂ) :
    integrand s u = u ^ (-s) * cexp (π * I * u ^ 2) *
      (cexp (π * I * u) - cexp (-(π * I * u)))⁻¹ := by
  unfold integrand kernel; ring

/-! ### Elementary bounds -/

/--
@isnad1 id=le.0h1v.s5.49a4caa2da53 from=translated src=- shape=ddf6c398 vocab=64f3ef88
-/
theorem abs_re_sub_im_le_sqrt_two_mul_norm (u : ℂ) : |u.re - u.im| ≤ Real.sqrt 2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul (by norm_num)]
  apply Real.abs_le_sqrt
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (u.re + u.im)]

/--
@isnad1 id=le.0h1v.s5.db3383a92b21 from=translated src=- shape=7b80b41c vocab=e43871ac
-/
theorem norm_le_abs_re_sub_im_add (u : ℂ) : ‖u‖ ≤ |u.re - u.im| + 2 * |u.im| := by
  refine (Complex.norm_le_abs_re_add_abs_im u).trans ?_
  have := abs_sub_abs_le_abs_sub u.re u.im
  linarith [abs_sub (u.re) (u.im)]

/--
@isnad1 id=le.0h2v.s5.bb6fd9719a93 from=translated src=- shape=f1b6e1e5 vocab=1c4837c4
-/
theorem norm_cpow_le_exp_pi (u w : ℂ) :
    ‖u ^ w‖ ≤ ‖u‖ ^ w.re * Real.exp (π * |w.im|) := by
  refine (Complex.norm_cpow_le u w).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg u * w.im) ≤ |arg u * w.im| := neg_le_abs _
    _ = |arg u| * |w.im| := abs_mul _ _
    _ ≤ π * |w.im| := by gcongr; exact Complex.abs_arg_le_pi u

/--
@isnad1 id=le.1h1v.s5.875aa4db77aa from=translated src=- shape=a62bbdcb vocab=349ddac6
-/
theorem abs_log_le_add_inv {y : ℝ} (hy : 0 < y) : |Real.log y| ≤ y + 1 / y := by
  have h1 : 0 < 1 / y := by positivity
  rcases le_or_gt 1 y with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    linarith [Real.log_le_sub_one_of_pos hy]
  · rw [abs_of_neg (Real.log_neg hy h), ← Real.log_inv, ← one_div]
    linarith [Real.log_le_sub_one_of_pos h1]

/--
@isnad1 id=le.1h2v.s6.8945951f38a0 from=translated src=- shape=187293bc vocab=c3f88876
-/
theorem rpow_neg_le_exp {y σ : ℝ} (hy : 0 < y) : y ^ (-σ) ≤ Real.exp (|σ| * (y + 1 / y)) := by
  rw [Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.2
  calc Real.log y * -σ ≤ |Real.log y * -σ| := le_abs_self _
    _ = |Real.log y| * |σ| := by rw [abs_mul, abs_neg]
    _ ≤ (y + 1 / y) * |σ| := by gcongr; exact abs_log_le_add_inv hy
    _ = |σ| * (y + 1 / y) := by ring

/--
@isnad1 id=eq.0h1v.s6.f5e7fe59ff7a from=translated src=- shape=5ef1fbf9 vocab=69cd1cfb
-/
theorem norm_exp_pi_I_mul_sq (u : ℂ) :
    ‖cexp (π * I * u ^ 2)‖ = Real.exp (-(2 * π) * u.re * u.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, sq, zero_mul, mul_zero,
    mul_one, sub_self, add_zero, zero_sub]
  ring

/-- A linear-times-Gaussian bound: `M |y| - 2 π y² ≤ M² / (4π) - π y²`.
@isnad1 id=le.0h2v.s7.52e1de0e4dcc from=translated src=- shape=46d892b6 vocab=7245c44e
-/
theorem mul_abs_sub_le (M y : ℝ) : M * |y| - 2 * π * y ^ 2 ≤ M ^ 2 / (4 * π) - π * y ^ 2 := by
  have hπ := Real.pi_pos
  have h := sq_nonneg (2 * π * |y| - M)
  have hy : |y| ^ 2 = y ^ 2 := sq_abs y
  rw [sub_le_sub_iff, ← sub_nonneg]
  have : M ^ 2 / (4 * π) - M * |y| + π * y ^ 2 = (2 * π * |y| - M) ^ 2 / (4 * π) := by
    field_simp; rw [← hy]; ring
  nlinarith [div_nonneg h (by positivity : (0 : ℝ) ≤ 4 * π)]

/-! ### The Gaussian bound on strips -/

/-- The constant of the Gaussian bound `norm_cpow_mul_exp_le` for `u^{-s} e^{iπu²}` on the strip
`c ≤ Re u - Im u ≤ c'`, for `|Re s| ≤ σ₀` and `|Im s| ≤ θ₀`.-/
@[expose] noncomputable def gaussConst (σ₀ θ₀ c c' : ℝ) : ℝ :=
  Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + (2 * σ₀ + 2 * π * c') ^ 2 / (4 * π))

/-- The constant of the Gaussian bound `norm_integrand_le` on the strip `c ≤ Re u - Im u ≤ c'`,
for `|Re s| ≤ σ₀`, `|Im s| ≤ θ₀` and lines at distance `≥ ρ` from the integers.-/
@[expose] noncomputable def boundConst (σ₀ θ₀ c c' ρ : ℝ) : ℝ :=
  Real.sqrt 2 / (4 * ρ) * gaussConst σ₀ θ₀ c c'

/--
@isnad1 id=le.1h5v.s5.33f54c49b9f3 from=translated src=- shape=9c937c55 vocab=06c5617b
-/
theorem boundConst_nonneg {σ₀ θ₀ c c' ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ boundConst σ₀ θ₀ c c' ρ := by
  unfold boundConst gaussConst; positivity

/-- The point `u` lies in `slitPlane` when `0 < Re u - Im u`.
@isnad1 id=mem.1h1v.s4.5f4ec34ee42a from=translated src=- shape=7b3920e3 vocab=63103e78
-/
theorem mem_slitPlane_of_re_sub_im_pos {u : ℂ} (hu : 0 < u.re - u.im) : u ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases h : u.im = 0
  · left; rw [h, sub_zero] at hu; exact hu
  · right; exact h

/--
@isnad1 id=ne.1h1v.s5.d29d99004931 from=translated src=- shape=3a21c75a vocab=41912c96
-/
theorem ne_zero_of_re_sub_im_pos {u : ℂ} (hu : 0 < u.re - u.im) : u ≠ 0 := by
  intro h; rw [h] at hu; simp at hu

/-- Bounds on `‖u‖` on the strip `c ≤ Re u - Im u ≤ c'`.
@isnad1 id=and.2h3v.s6.3dd5ca11bc5f from=translated src=- shape=571249d1 vocab=cabe2fb4
-/
theorem norm_bounds_of_strip {u : ℂ} {c c' : ℝ} (hc : 0 < c) (hu : u.re - u.im ∈ Icc c c') :
    1 / ‖u‖ ≤ Real.sqrt 2 / c ∧ ‖u‖ ≤ c' + 2 * |u.im| := by
  have hκ0 : 0 < u.re - u.im := hc.trans_le hu.1
  have hnorm0 : 0 < ‖u‖ := norm_pos_iff.2 (ne_zero_of_re_sub_im_pos hκ0)
  have hlow : u.re - u.im ≤ Real.sqrt 2 * ‖u‖ := by
    have := abs_re_sub_im_le_sqrt_two_mul_norm u
    rwa [abs_of_pos hκ0] at this
  constructor
  · rw [div_le_div_iff₀ hnorm0 hc]
    nlinarith [hu.1]
  · have := norm_le_abs_re_sub_im_add u
    rw [abs_of_pos hκ0] at this
    linarith [hu.2]

/-- `‖e^{iπu²}‖ ≤ exp (2 π c' |Im u| - 2 π (Im u)²)` on the strip `c ≤ Re u - Im u ≤ c'`.
@isnad1 id=le.2h3v.s7.08291181cb1c from=translated src=- shape=b31806b0 vocab=64721523
-/
theorem norm_exp_pi_I_mul_sq_le {u : ℂ} {c c' : ℝ} (hc : 0 < c) (hu : u.re - u.im ∈ Icc c c') :
    ‖cexp (π * I * u ^ 2)‖ ≤ Real.exp (2 * π * c' * |u.im| - 2 * π * u.im ^ 2) := by
  rw [norm_exp_pi_I_mul_sq]
  apply Real.exp_le_exp.2
  set κ := u.re - u.im with hκ
  have hκ0 : 0 < κ := hc.trans_le hu.1
  have hre : u.re = u.im + κ := by rw [hκ]; ring
  rw [hre]
  have h1 : -(2 * π) * κ * u.im ≤ 2 * π * c' * |u.im| := by
    have : -(2 * π) * κ * u.im ≤ |2 * π * κ * u.im| := by
      rw [show -(2 * π) * κ * u.im = -(2 * π * κ * u.im) by ring]; exact neg_le_abs _
    refine this.trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π * κ)]
    gcongr
    exact hu.2
  nlinarith

/-- The Gaussian bound for `u^{-s} e^{iπu²}` on the strip `c ≤ Re u - Im u ≤ c'`.
@isnad1 id=le.4h6v.s7.5c335b6a258c from=translated src=- shape=019fc020 vocab=3569fbbc
-/
theorem norm_cpow_mul_exp_le {s u : ℂ} {σ₀ θ₀ c c' : ℝ} (hσ₀ : |s.re| ≤ σ₀) (hθ₀ : |s.im| ≤ θ₀)
    (hc : 0 < c) (hu : u.re - u.im ∈ Icc c c') :
    ‖u ^ (-s) * cexp (π * I * u ^ 2)‖ ≤ gaussConst σ₀ θ₀ c c' * Real.exp (-π * u.im ^ 2) := by
  set y := u.im with hy
  have hκ0 : 0 < u.re - u.im := hc.trans_le hu.1
  have hu0 : u ≠ 0 := ne_zero_of_re_sub_im_pos hκ0
  have hnorm0 : 0 < ‖u‖ := norm_pos_iff.2 hu0
  obtain ⟨hinv, hup⟩ := norm_bounds_of_strip hc hu
  have hσ₀0 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ₀
  have hpow : ‖u ^ (-s)‖ ≤
      Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) := by
    have h := norm_cpow_le_exp_pi u (-s)
    rw [neg_re, neg_im, abs_neg] at h
    refine h.trans ?_
    calc ‖u‖ ^ (-s.re) * Real.exp (π * |s.im|)
        ≤ Real.exp (|s.re| * (‖u‖ + 1 / ‖u‖)) * Real.exp (π * |s.im|) :=
          mul_le_mul_of_nonneg_right (rpow_neg_le_exp hnorm0) (Real.exp_pos _).le
      _ ≤ Real.exp (σ₀ * (c' + 2 * |y| + Real.sqrt 2 / c)) * Real.exp (π * θ₀) := by
          have h1 : |s.re| * (‖u‖ + 1 / ‖u‖) ≤ σ₀ * (c' + 2 * |y| + Real.sqrt 2 / c) := by
            have : 0 ≤ ‖u‖ + 1 / ‖u‖ := by positivity
            calc |s.re| * (‖u‖ + 1 / ‖u‖) ≤ σ₀ * (‖u‖ + 1 / ‖u‖) := by gcongr
              _ ≤ σ₀ * (c' + 2 * |y| + Real.sqrt 2 / c) := by gcongr
          have h2 : π * |s.im| ≤ π * θ₀ := by gcongr
          exact mul_le_mul (Real.exp_le_exp.2 h1) (Real.exp_le_exp.2 h2) (Real.exp_pos _).le
            (Real.exp_pos _).le
      _ = Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) := by
          rw [← Real.exp_add]; congr 1; ring
  have hexp := norm_exp_pi_I_mul_sq_le hc hu
  rw [norm_mul]
  calc ‖u ^ (-s)‖ * ‖cexp (π * I * u ^ 2)‖
      ≤ Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) *
          Real.exp (2 * π * c' * |y| - 2 * π * y ^ 2) := by gcongr
    _ = Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) +
          ((2 * σ₀ + 2 * π * c') * |y| - 2 * π * y ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) +
          ((2 * σ₀ + 2 * π * c') ^ 2 / (4 * π) - π * y ^ 2)) := by
        apply Real.exp_le_exp.2
        linarith [mul_abs_sub_le (2 * σ₀ + 2 * π * c') y]
    _ = gaussConst σ₀ θ₀ c c' * Real.exp (-π * u.im ^ 2) := by
        unfold gaussConst
        rw [← hy, ← Real.exp_add]
        congr 1; ring

/-- `‖1 / (e^{iπu} - e^{-iπu})‖ ≤ √2 / (4 ρ)` when `Re u - Im u` is at distance `≥ ρ` from the
integers.
@isnad1 id=le.2h2v.s7.e660e26674c6 from=translated src=- shape=4d386fda vocab=a3d496a7
-/
theorem norm_inv_exp_sub_exp_neg_le {u : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ m : ℤ, ρ ≤ |u.re - u.im - m|) :
    ‖(cexp (π * I * u) - cexp (-(π * I * u)))⁻¹‖ ≤ Real.sqrt 2 / (4 * ρ) := by
  rw [exp_sub_exp_neg_eq_two_I_sin, norm_inv, norm_mul, norm_mul, Complex.norm_two, Complex.norm_I,
    mul_one]
  set m : ℤ := round u.re with hm
  have hre : |u.re - m| ≤ 1 / 2 := by rw [hm]; exact abs_sub_round u.re
  have h1 := two_mul_norm_sub_le_norm_sin_pi_mul u m hre
  have h2 : ρ ≤ Real.sqrt 2 * ‖u - m‖ := by
    refine (hu m).trans ?_
    have := abs_re_sub_im_le_sqrt_two_mul_norm (u - m)
    rwa [sub_re, sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero, sub_right_comm]
      at this
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsin : 0 < ‖Complex.sin (π * u)‖ := by
    have : 0 < ‖u - m‖ := by nlinarith
    linarith
  rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ hs2]
  nlinarith

/-- The Gaussian bound on the strip `c ≤ Re u - Im u ≤ c'`:
`‖integrand s u‖ ≤ boundConst σ₀ θ₀ c c' ρ * exp (-π (Im u)²)` when `|Re s| ≤ σ₀`, `|Im s| ≤ θ₀`,
`0 < c` and every `κ ∈ [c, c']` is at distance `≥ ρ` from the integers.
@isnad1 id=le.6h7v.s7.d4a7ed5ad0b9 from=translated src=- shape=8e5be094 vocab=1d9ab516
-/
theorem norm_integrand_le {s u : ℂ} {σ₀ θ₀ c c' ρ : ℝ} (hσ₀ : |s.re| ≤ σ₀) (hθ₀ : |s.im| ≤ θ₀)
    (hc : 0 < c) (hρ : 0 < ρ) (hstrip : ∀ κ ∈ Icc c c', ∀ m : ℤ, ρ ≤ |κ - m|)
    (hu : u.re - u.im ∈ Icc c c') :
    ‖integrand s u‖ ≤ boundConst σ₀ θ₀ c c' ρ * Real.exp (-π * u.im ^ 2) := by
  have h1 := norm_cpow_mul_exp_le hσ₀ hθ₀ hc hu
  have h2 := norm_inv_exp_sub_exp_neg_le hρ (hstrip _ hu)
  rw [integrand_eq_gauss_mul, norm_mul]
  calc ‖u ^ (-s) * cexp (π * I * u ^ 2)‖ * ‖(cexp (π * I * u) - cexp (-(π * I * u)))⁻¹‖
      ≤ gaussConst σ₀ θ₀ c c' * Real.exp (-π * u.im ^ 2) * (Real.sqrt 2 / (4 * ρ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = boundConst σ₀ θ₀ c c' ρ * Real.exp (-π * u.im ^ 2) := by unfold boundConst; ring

/-! ### The lines `u = c - ω x` -/

/--
@isnad1 id=eq.0h2v.s5.72a1e6881264 from=translated src=- shape=31535dfc vocab=3f20781b
-/
theorem re_sub_im_line (c x : ℝ) : ((c : ℂ) - ω * x).re - ((c : ℂ) - ω * x).im = c := by
  rw [re_sub_im_sub_rsOmega_mul]; simp

/--
@isnad1 id=eq.0h2v.s5.83ffb6dd2d42 from=translated src=- shape=7c75dd70 vocab=a5e7c96a
-/
theorem im_line (c x : ℝ) : ((c : ℂ) - ω * x).im = -(Real.sqrt 2 / 2) * x := by
  rw [im_sub_rsOmega_mul]; simp

/--
@isnad1 id=eq.0h2v.s6.abb65f5cc8de from=translated src=- shape=c8ef9dda vocab=85b86961
-/
theorem im_line_sq (c x : ℝ) : ((c : ℂ) - ω * x).im ^ 2 = x ^ 2 / 2 := by
  rw [im_line, mul_pow, neg_sq, sqrt_two_div_two_sq]; ring

/--
@isnad1 id=le.0h2v.s5.58635797480a from=translated src=- shape=b681d3ab vocab=f4675402
-/
theorem abs_im_line_le (c x : ℝ) : |((c : ℂ) - ω * x).im| ≤ |x| := by
  rw [im_line, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2 / 2)]
  have h1 : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have := abs_nonneg x
  nlinarith

/--
@isnad1 id=mem.1h2v.s5.46cc71fbe5f1 from=translated src=- shape=fe5f6e11 vocab=9ec96993
-/
theorem line_mem_slitPlane {c : ℝ} (hc0 : 0 < c) (x : ℝ) : (c : ℂ) - ω * x ∈ slitPlane :=
  mem_slitPlane_of_re_sub_im_pos (by rw [re_sub_im_line]; exact hc0)

/--
@isnad1 id=ne.1h2v.s5.0e0afb48efd6 from=translated src=- shape=5d3f9ad3 vocab=2a4d29d5
-/
theorem line_ne_zero {c : ℝ} (hc0 : 0 < c) (x : ℝ) : (c : ℂ) - ω * x ≠ 0 :=
  ne_zero_of_re_sub_im_pos (by rw [re_sub_im_line]; exact hc0)

/--
@isnad1 id=continuo.2h2v.s6.6e82f830e01a from=translated src=- shape=6d9f89f6 vocab=14d2bc14
-/
theorem continuous_integrand_line (s : ℂ) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    Continuous fun x : ℝ => integrand s (c - ω * x) := by
  unfold integrand kernel
  refine Continuous.mul ?_
    (Continuous.div (by fun_prop) (by fun_prop) (mordell_denom_line_ne_zero hc))
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hf : ContinuousAt (fun x : ℝ => (c : ℂ) - ω * x) x := by fun_prop
  exact ContinuousAt.comp (g := fun u : ℂ => u ^ (-s))
    (continuousAt_cpow_const (line_mem_slitPlane hc0 x)) hf

/--
@isnad1 id=continuo.1h1v.s5.0725a12c6c22 from=translated src=- shape=ea74a74f vocab=9aa62485
-/
theorem continuous_log_line {c : ℝ} (hc0 : 0 < c) :
    Continuous fun x : ℝ => Complex.log (c - ω * x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hf : ContinuousAt (fun x : ℝ => (c : ℂ) - ω * x) x := by fun_prop
  exact ContinuousAt.comp (g := Complex.log) (continuousAt_clog (line_mem_slitPlane hc0 x)) hf

/--
@isnad1 id=le.1h3v.s5.afcb2c9bac98 from=translated src=- shape=5acaeaee vocab=1ec01bc7
-/
theorem strip_dist_line (c : ℝ) : ∀ κ ∈ Icc c c, ∀ m : ℤ, |c - round c| ≤ |κ - m| := by
  intro κ hκ m
  rw [Icc_self, mem_singleton_iff] at hκ
  rw [hκ]; exact round_le c m

/--
@isnad1 id=le.4h5v.s7.c2a4cfd56676 from=translated src=- shape=3ce0e459 vocab=e202c9bb
-/
theorem norm_integrand_line_le {s : ℂ} {σ₀ θ₀ : ℝ} (hσ₀ : |s.re| ≤ σ₀) (hθ₀ : |s.im| ≤ θ₀)
    {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) :
    ‖integrand s (c - ω * x)‖ ≤
      boundConst σ₀ θ₀ c c |c - round c| * Real.exp (-(π / 2) * x ^ 2) := by
  have := norm_integrand_le hσ₀ hθ₀ hc0 (dist_round_pos hc) (strip_dist_line c)
    (u := c - ω * x) (by rw [re_sub_im_line]; exact ⟨le_rfl, le_rfl⟩)
  rwa [im_line_sq, show -π * (x ^ 2 / 2) = -(π / 2) * x ^ 2 by ring] at this

/--
@isnad1 id=integrab.2h2v.s6.7711f4020743 from=translated src=- shape=4e5b248f vocab=a4fd3b63
-/
theorem integrable_integrand_line (s : ℂ) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    Integrable fun x : ℝ => integrand s (c - ω * x) :=
  integrable_of_norm_le_gaussian (by positivity) (continuous_integrand_line s hc0 hc)
    (norm_integrand_line_le le_rfl le_rfl hc0 hc)

/-! ### Differentiability in `s` -/

/--
@isnad1 id=le.2h3v.s6.cd3452b7db56 from=translated src=- shape=ae7631af vocab=a028cb82
-/
theorem norm_log_le_of_strip {u : ℂ} {c c' : ℝ} (hc : 0 < c) (hu : u.re - u.im ∈ Icc c c') :
    ‖Complex.log u‖ ≤ c' + Real.sqrt 2 / c + π + 2 * |u.im| := by
  have hκ0 : 0 < u.re - u.im := hc.trans_le hu.1
  have hu0 := ne_zero_of_re_sub_im_pos hκ0
  have hnorm0 : 0 < ‖u‖ := norm_pos_iff.2 hu0
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  have h1 := abs_log_le_add_inv hnorm0
  have h2 := Complex.abs_arg_le_pi u
  have hlow : u.re - u.im ≤ Real.sqrt 2 * ‖u‖ := by
    have := abs_re_sub_im_le_sqrt_two_mul_norm u
    rwa [abs_of_pos hκ0] at this
  have hinv : 1 / ‖u‖ ≤ Real.sqrt 2 / c := by
    rw [div_le_div_iff₀ hnorm0 hc]
    nlinarith [hu.1]
  have hup : ‖u‖ ≤ c' + 2 * |u.im| := by
    have := norm_le_abs_re_sub_im_add u
    rw [abs_of_pos hκ0] at this
    linarith [hu.2]
  linarith

/--
@isnad1 id=hasderiv.1h2v.s6.37449fba2913 from=translated src=- shape=c9266d0e vocab=6e483f84
-/
theorem hasDerivAt_integrand {u : ℂ} (hu : u ≠ 0) (s : ℂ) :
    HasDerivAt (fun s => integrand s u) (-(Complex.log u * integrand s u)) s := by
  unfold integrand
  exact (((hasDerivAt_neg s).const_cpow (c := u) (Or.inl hu)).mul_const (kernel u)).congr_deriv
    (by ring)

/--
@isnad1 id=le.4h5v.s8.efbab2dc6788 from=translated src=- shape=f3b1375e vocab=484a42f2
-/
theorem norm_log_mul_integrand_line_le {s : ℂ} {σ₀ θ₀ : ℝ} (hσ₀ : |s.re| ≤ σ₀)
    (hθ₀ : |s.im| ≤ θ₀) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) :
    ‖Complex.log (c - ω * x) * integrand s (c - ω * x)‖ ≤
      (c + Real.sqrt 2 / c + π + 2 + 4 / π) * boundConst σ₀ θ₀ c c |c - round c| *
        Real.exp (-(π / 4) * x ^ 2) := by
  rw [norm_mul]
  have h1 := norm_log_le_of_strip hc0 (u := c - ω * x)
    (by rw [re_sub_im_line]; exact ⟨le_rfl, le_rfl⟩)
  have h2 := norm_integrand_line_le hσ₀ hθ₀ hc0 hc x
  have h3 := abs_im_line_le c x
  have hK := boundConst_nonneg (σ₀ := σ₀) (θ₀ := θ₀) (c := c) (c' := c) (dist_round_pos hc)
  set A : ℝ := c + Real.sqrt 2 / c + π with hA
  set K := boundConst σ₀ θ₀ c c |c - round c| with hK'
  have hA0 : 0 ≤ A := by positivity
  have hπ : 0 < π / 2 := by positivity
  calc ‖Complex.log (c - ω * x)‖ * ‖integrand s (c - ω * x)‖
      ≤ (A + 2 * |x|) * (K * Real.exp (-(π / 2) * x ^ 2)) :=
        mul_le_mul (h1.trans (show A + 2 * |((c : ℂ) - ω * x).im| ≤ A + 2 * |x| by linarith)) h2
          (norm_nonneg _) (by positivity : (0 : ℝ) ≤ A + 2 * |x|)
    _ = K * ((A + 2 * |x|) * Real.exp (-(π / 2) * x ^ 2)) := by ring
    _ ≤ K * ((A + 2 + 2 / (π / 2)) * Real.exp (-(π / 2 / 2) * x ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (affine_mul_exp_neg_sq_le (B := 2) hπ hA0 (by norm_num) x)
          hK
    _ = (A + 2 + 4 / π) * K * Real.exp (-(π / 4) * x ^ 2) := by
        rw [show π / 2 / 2 = π / 4 by ring, show 2 / (π / 2) = 4 / π by rw [div_div_eq_mul_div]; norm_num]
        ring

/--
@isnad1 id=and.1h2v.s6.2ca126e35573 from=translated src=- shape=fce7cfb7 vocab=55510a73
-/
theorem abs_re_le_of_mem_ball {s s₀ : ℂ} (hs : s ∈ Metric.ball s₀ 1) :
    |s.re| ≤ |s₀.re| + 1 ∧ |s.im| ≤ |s₀.im| + 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have h1 := Complex.abs_re_le_norm (s - s₀)
  have h2 := Complex.abs_im_le_norm (s - s₀)
  rw [sub_re] at h1
  rw [sub_im] at h2
  constructor
  · calc |s.re| = |(s.re - s₀.re) + s₀.re| := by ring_nf
      _ ≤ |s.re - s₀.re| + |s₀.re| := abs_add_le _ _
      _ ≤ |s₀.re| + 1 := by linarith
  · calc |s.im| = |(s.im - s₀.im) + s₀.im| := by ring_nf
      _ ≤ |s.im - s₀.im| + |s₀.im| := abs_add_le _ _
      _ ≤ |s₀.im| + 1 := by linarith

/-- The Riemann–Siegel integral is differentiable in `s`, with derivative obtained by
differentiating under the integral sign.
@isnad1 id=hasderiv.2h2v.s7.427cde875b6c from=translated src=- shape=5e62b80e vocab=68367e55
-/
theorem hasDerivAt_rsIntegral (s₀ : ℂ) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    HasDerivAt (fun s => rsIntegral s c)
      (∫ x : ℝ, -ω * -(Complex.log (c - ω * x) * integrand s₀ (c - ω * x))) s₀ := by
  unfold rsIntegral
  set σ₀ : ℝ := |s₀.re| + 1 with hσ₀
  set θ₀ : ℝ := |s₀.im| + 1 with hθ₀
  set K : ℝ := (c + Real.sqrt 2 / c + π + 2 + 4 / π) * boundConst σ₀ θ₀ c c |c - round c|
    with hK
  have hmeas : ∀ s : ℂ,
      AEStronglyMeasurable (fun x : ℝ => -ω * integrand s (c - ω * x)) volume :=
    fun s => (continuous_const.mul (continuous_integrand_line s hc0 hc)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall hmeas) ((integrable_integrand_line s₀ hc0 hc).const_mul _)
    (F' := fun s x => -ω * -(Complex.log (c - ω * x) * integrand s (c - ω * x)))
    ?_ (bound := fun x => K * Real.exp (-(π / 4) * x ^ 2)) ?_ ?_ ?_).2
  · exact (continuous_const.mul ((continuous_log_line hc0).mul
      (continuous_integrand_line s₀ hc0 hc)).neg).aestronglyMeasurable
  · refine Eventually.of_forall fun x s hs => ?_
    rw [norm_mul, norm_neg, norm_rsOmega, one_mul, norm_neg]
    obtain ⟨h1, h2⟩ := abs_re_le_of_mem_ball hs
    exact norm_log_mul_integrand_line_le h1 h2 hc0 hc x
  · exact (integrable_exp_neg_mul_sq (by positivity)).const_mul K
  · refine Eventually.of_forall fun x s _ => ?_
    exact (hasDerivAt_integrand (line_ne_zero hc0 x) s).const_mul (-ω)

/-- The Riemann–Siegel integral is an entire function of `s`.
@isnad1 id=differen.2h1v.s6.3433802292d3 from=translated src=- shape=de82ff39 vocab=bdca3dee
-/
theorem differentiable_rsIntegral {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    Differentiable ℂ fun s => rsIntegral s c :=
  fun s => (hasDerivAt_rsIntegral s hc0 hc).differentiableAt

/-! ### Crossing a pole -/

/-- The numerator `u^{-s} e^{iπu²} (-1)^n mordellS (u - n)`: holomorphic near `u = n`, with
`integrand s u = poleNumerator s n u / (u - n)` away from the integers.-/
@[expose] noncomputable def poleNumerator (s : ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  u ^ (-s) * cexp (π * I * u ^ 2) * ((-1) ^ n * mordellS (u - n))

/--
@isnad1 id=eq.2h3v.s6.26e4e927c592 from=translated src=- shape=0da2ebbe vocab=08601ada
-/
theorem integrand_eq_poleNumerator_div {s u : ℂ} (n : ℕ) (hu : Complex.sin (π * u) ≠ 0)
    (hun : u ≠ n) : integrand s u = poleNumerator s n u / (u - n) := by
  have hsin : Complex.sin (π * (u - n)) = (-1) ^ n * Complex.sin (π * u) := by
    rw [mul_sub, mul_comm (π : ℂ) (n : ℂ)]
    exact Complex.sin_antiperiodic.sub_nat_mul_eq n
  unfold integrand kernel poleNumerator
  rw [exp_sub_exp_neg_eq_two_I_sin, mordellS, sincPi_of_ne (sub_ne_zero.2 hun), hsin]
  have h1 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : u - n ≠ 0 := sub_ne_zero.2 hun
  have h3 : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

/--
@isnad1 id=eq.0h2v.s5.04a5cd3ba309 from=translated src=- shape=7c15fa10 vocab=c5201b8d
-/
theorem poleNumerator_apply_self (s : ℂ) (n : ℕ) :
    poleNumerator s n n = (n : ℂ) ^ (-s) / (2 * π * I) := by
  unfold poleNumerator
  rw [sub_self, mordellS_zero]
  have h1 : cexp (π * I * (n : ℂ) ^ 2) = (-1) ^ (n ^ 2) := by
    rw [show (π : ℂ) * I * (n : ℂ) ^ 2 = ((n ^ 2 : ℕ) : ℂ) * (π * I) by push_cast; ring,
      Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have h2 : (-1 : ℂ) ^ (n ^ 2) * (-1) ^ n = 1 := by
    rw [← pow_add]
    refine Even.neg_one_pow ?_
    rw [sq, ← mul_add_one]
    exact Nat.even_mul_succ_self n
  rw [h1]
  calc (n : ℂ) ^ (-s) * (-1) ^ (n ^ 2) * ((-1) ^ n * (1 / (2 * π * I)))
      = (n : ℂ) ^ (-s) * ((-1) ^ (n ^ 2) * (-1) ^ n) * (1 / (2 * π * I)) := by ring
    _ = (n : ℂ) ^ (-s) / (2 * π * I) := by rw [h2]; ring

/--
@isnad1 id=differen.2h3v.s6.463c8b751743 from=translated src=- shape=82453a65 vocab=e6e9638e
-/
theorem differentiableAt_poleNumerator {s u : ℂ} {n : ℕ} (hu : 0 < u.re - u.im)
    (hun : ∀ m : ℤ, m ≠ 0 → u ≠ n + m) :
    DifferentiableAt ℂ (poleNumerator s n) u := by
  unfold poleNumerator
  have h1 : DifferentiableAt ℂ (fun u : ℂ => u ^ (-s)) u :=
    differentiableAt_id.cpow_const (mem_slitPlane_of_re_sub_im_pos hu)
  have h2 : DifferentiableAt ℂ (fun u : ℂ => mordellS (u - n)) u := by
    refine (differentiableAt_mordellS ?_).comp u (differentiableAt_id.sub_const _)
    refine sincPi_ne_zero_of_ne_int fun m hm h => hun m hm ?_
    linear_combination h
  exact (h1.mul (by fun_prop)).mul ((differentiableAt_const _).mul h2)

/-- On the strip `c ≤ κ ≤ c'`, the integers other than `n` are at distance at least
`min (c - (n - 1)) (n + 1 - c')` from `κ`.
@isnad1 id=le.2h5v.s6.52544a195b04 from=translated src=- shape=dbed1b2d vocab=736c36d7
-/
theorem min_le_abs_sub_nat_add_int {c c' : ℝ} (n : ℕ) {κ : ℝ} (hκ : κ ∈ Icc c c') (m : ℤ)
    (hm : m ≠ 0) :
    min (c - (n - 1)) (n + 1 - c') ≤ |κ - (n + m)| := by
  rcases lt_or_gt_of_ne hm with h | h
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
    refine (min_le_left _ _).trans (le_trans ?_ (le_abs_self _))
    linarith [hκ.1]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    refine (min_le_right _ _).trans (le_trans ?_ (neg_le_abs _))
    linarith [hκ.2]

theorem eq_nat_of_mem_strip {c c' : ℝ} {n : ℕ} (hcn : (n : ℝ) - 1 < c) (hc'n : c' < n + 1)
    {u : ℂ} (hu : u.re - u.im ∈ Icc c c') (m : ℤ) (hm : m ≠ 0) : u ≠ n + m := by
  intro h
  rw [h] at hu
  simp only [add_re, add_im, natCast_re, natCast_im, intCast_re, intCast_im, add_zero] at hu
  have h1 : (-1 : ℝ) < m := by linarith [hu.1, hcn]
  have h2 : (m : ℝ) < 1 := by linarith [hu.2, hc'n]
  have h1' : (-1 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- The pole numerator satisfies a Gaussian bound on the strip `c ≤ Re u - Im u ≤ c'` when
`n` is the only integer in `[c, c']`.
@isnad1 id=ex.3h4v.s7.b2ed1c4081cc from=translated src=- shape=4395d8de vocab=65e15cbf
-/
theorem exists_norm_poleNumerator_le (s : ℂ) {c c' : ℝ} {n : ℕ} (hc : 0 < c)
    (hcn : (n : ℝ) - 1 < c) (hc'n : c' < n + 1) :
    ∃ C : ℝ, ∀ u : ℂ, u.re - u.im ∈ Icc c c' →
      ‖poleNumerator s n u‖ ≤ C * Real.exp (-(π / 2) * u.im ^ 2) := by
  set δ : ℝ := min (c - (n - 1)) (n + 1 - c') with hδ
  by_cases hcc' : c ≤ c'
  swap
  · refine ⟨0, fun u hu => ?_⟩
    exact absurd (hu.1.trans hu.2) hcc'
  have hδ0 : 0 < δ := by
    rw [hδ]; exact lt_min (by linarith) (by linarith)
  set ρ : ℝ := δ / Real.sqrt 2 with hρ
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hρ0 : 0 < ρ := by positivity
  set G := gaussConst |s.re| |s.im| c c' with hG
  have hG0 : 0 < G := Real.exp_pos _
  set A : ℝ := 1 / 4 + (c' + n) / (4 * ρ) with hA
  set B : ℝ := 2 / (4 * ρ) with hB
  have hc'0 : 0 < c' := hc.trans_le hcc'
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (c' + n) / (4 * ρ) :=
      div_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
    rw [hA]; linarith
  have hB0 : 0 ≤ B := by positivity
  refine ⟨G * (A + B + B / π), fun u hu => ?_⟩
  have hgauss := norm_cpow_mul_exp_le (s := s) le_rfl le_rfl hc hu
  obtain ⟨-, hup⟩ := norm_bounds_of_strip hc hu
  -- the `mordellS` factor
  have hdist : ∀ m : ℤ, m ≠ 0 → ρ ≤ ‖u - n - m‖ := by
    intro m hm
    have h1 := min_le_abs_sub_nat_add_int n hu m hm
    have h2 := abs_re_sub_im_le_sqrt_two_mul_norm (u - n - m)
    simp only [sub_re, sub_im, natCast_re, natCast_im, intCast_re, intCast_im, sub_zero] at h2
    rw [hρ, div_le_iff₀ hs2]
    calc δ ≤ |u.re - u.im - (n + m)| := h1
      _ = |u.re - n - m - u.im| := by ring_nf
      _ ≤ Real.sqrt 2 * ‖u - n - m‖ := h2
      _ = ‖u - n - m‖ * Real.sqrt 2 := mul_comm _ _
  have hS := norm_mordellS_le hρ0 hdist
  have hun : ‖u - n‖ ≤ c' + n + 2 * |u.im| := by
    calc ‖u - n‖ ≤ ‖u‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ = ‖u‖ + n := by rw [Complex.norm_natCast]
      _ ≤ c' + n + 2 * |u.im| := by linarith
  have hS' : ‖(-1 : ℂ) ^ n * mordellS (u - n)‖ ≤ A + B * |u.im| := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine hS.trans ?_
    rw [hA, hB]
    have : ‖u - n‖ / (4 * ρ) ≤ (c' + n + 2 * |u.im|) / (4 * ρ) := by gcongr
    have e : (c' + n + 2 * |u.im|) / (4 * ρ) = (c' + n) / (4 * ρ) + 2 / (4 * ρ) * |u.im| := by ring
    linarith
  unfold poleNumerator
  rw [norm_mul]
  calc ‖u ^ (-s) * cexp (π * I * u ^ 2)‖ * ‖(-1 : ℂ) ^ n * mordellS (u - n)‖
      ≤ G * Real.exp (-π * u.im ^ 2) * (A + B * |u.im|) :=
        mul_le_mul hgauss hS' (norm_nonneg _) (by positivity)
    _ = G * ((A + B * |u.im|) * Real.exp (-π * u.im ^ 2)) := by ring
    _ ≤ G * ((A + B + B / π) * Real.exp (-(π / 2) * u.im ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (affine_mul_exp_neg_sq_le Real.pi_pos hA0 hB0 u.im) hG0.le
    _ = G * (A + B + B / π) * Real.exp (-(π / 2) * u.im ^ 2) := by ring

/--
@isnad1 id=ne.1h2v.s5.88804978c75e from=translated src=- shape=d254f803 vocab=727f4afa
-/
theorem sin_line_ne_zero {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) :
    Complex.sin (π * ((c : ℂ) - ω * x)) ≠ 0 := by
  have := mordell_denom_line_ne_zero hc x
  rw [exp_sub_exp_neg_eq_two_I_sin] at this
  exact right_ne_zero_of_mul this

/--
@isnad1 id=ne.1h3v.s5.273b3a357d01 from=translated src=- shape=169a07c3 vocab=dbfa5850
-/
theorem line_ne_nat {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) (n : ℕ) : (c : ℂ) - ω * x ≠ n := by
  intro h
  have := re_sub_im_line c x
  rw [h] at this
  simp only [natCast_re, natCast_im, sub_zero] at this
  exact hc n (by rw [← this]; simp)

/-- Moving the Riemann–Siegel line from `c` to `c'` across the single integer `n ∈ (c, c')`
subtracts the residue term `n^{-s}`.
@isnad1 id=eq.5h4v.s6.3c15877c803b from=translated src=- shape=60ad2905 vocab=2a039f1c
-/
theorem rsIntegral_eq_sub_of_lt (s : ℂ) {c c' : ℝ} {n : ℕ} (hc : 0 < c) (hcn : (n : ℝ) - 1 < c)
    (hcn' : c < n) (hnc' : (n : ℝ) < c') (hc'n : c' < n + 1) :
    rsIntegral s c' = rsIntegral s c - (n : ℂ) ^ (-s) := by
  obtain ⟨C, hC⟩ := exists_norm_poleNumerator_le s hc hcn hc'n
  have hc' : 0 < c' := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcZ : ∀ m : ℤ, c ≠ m := by
    intro m h
    have h1 : (n : ℝ) - 1 < m := by rw [← h]; exact hcn
    have h2 : (m : ℝ) < n := by rw [← h]; exact hcn'
    have h1' : (n : ℤ) - 1 < m := by exact_mod_cast h1
    have h2' : m < (n : ℤ) := by exact_mod_cast h2
    omega
  have hc'Z : ∀ m : ℤ, c' ≠ m := by
    intro m h
    have h1 : (n : ℝ) < m := by rw [← h]; exact hnc'
    have h2 : (m : ℝ) < n + 1 := by rw [← h]; exact hc'n
    have h1' : (n : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (n : ℤ) + 1 := by exact_mod_cast h2
    omega
  have key := integral_rsLine_sub_eq_of_pole (N := poleNumerator s n) (p := n) (a := π / 2)
    (C := C) (by positivity) (by simpa using hcn') (by simpa using hnc')
    (fun u hu => differentiableAt_poleNumerator (hc.trans_le hu.1) (eq_nat_of_mem_strip hcn hc'n hu))
    hC
  rw [poleNumerator_apply_self] at key
  have e1 : ∀ x : ℝ, -ω * (poleNumerator s n (c' - ω * x) / (c' - ω * x - n)) =
      -ω * integrand s (c' - ω * x) := fun x => by
    rw [integrand_eq_poleNumerator_div n (sin_line_ne_zero hc'Z x) (line_ne_nat hc'Z x n)]
  have e2 : ∀ x : ℝ, -ω * (poleNumerator s n (c - ω * x) / (c - ω * x - n)) =
      -ω * integrand s (c - ω * x) := fun x => by
    rw [integrand_eq_poleNumerator_div n (sin_line_ne_zero hcZ x) (line_ne_nat hcZ x n)]
  simp_rw [e1, e2] at key
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have e3 : -2 * π * I * ((n : ℂ) ^ (-s) / (2 * π * I)) = -(n : ℂ) ^ (-s) := by
    field_simp
  rw [e3] at key
  unfold rsIntegral
  linear_combination key

/-- `R(s, N + 1/2) = R(s, 1/2) - ∑_{n=1}^{N} n^{-s}`.
@isnad1 id=eq.0h2v.s6.f7ef51812547 from=translated src=- shape=af3fe199 vocab=aae9b752
-/
theorem rsIntegral_add_half (s : ℂ) (N : ℕ) :
    rsIntegral s (N + 1 / 2) = rsIntegral s (1 / 2) - ∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ← ih]
    have := rsIntegral_eq_sub_of_lt s (c := N + 1 / 2) (c' := N + 1 + 1 / 2) (n := N + 1)
      (by positivity) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)
    push_cast at this ⊢
    exact this

end RiemannSiegel
