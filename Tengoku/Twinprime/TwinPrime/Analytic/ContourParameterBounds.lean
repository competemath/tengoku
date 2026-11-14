import Tengoku.Twinprime.TwinPrime.Analytic.MellinTruncation
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary parameter estimates for the Mellin rectangles

The right line `1+1/log x` costs exactly a factor `exp 1` in `x^c`.
A width bounded below by `k(log x)^(-1/2)` gives exponential decay
that absorbs every fixed logarithmic power.
-/

noncomputable section

open Filter
open scoped Topology

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.1h1v.s6.98953e5906b9 from=translated src=- shape=8f8e9db3 vocab=25172127
-/
theorem rpow_one_add_inv_log (x : ℝ) (hx : 1 < x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
  have he : Real.log x * (1 / Real.log x) = 1 := by field_simp
  rw [he]
  ring

/--
@isnad1 id=eq.1h2v.s5.06574d31d0d7 from=translated src=- shape=890913e6 vocab=dac88f51
-/
theorem rpow_one_sub_eq_mul_exp (x δ : ℝ) (hx : 0 < x) :
    x ^ (1 - δ) = x * Real.exp (-δ * Real.log x) := by
  rw [show 1 - δ = 1 + -δ by ring, Real.rpow_add hx, Real.rpow_one,
    Real.rpow_def_of_pos hx]
  congr 2
  ring

/--
@isnad1 id=le.2h3v.s7.c3c04786a2e3 from=translated src=- shape=bf466ebe vocab=35853818
-/
theorem rpow_one_sub_le_of_width (x k δ : ℝ) (hx : 1 < x)
    (hwidth : k * (Real.log x) ^ (-(1 / 2 : ℝ)) ≤ δ) :
    x ^ (1 - δ) ≤ x * Real.exp (-k * (Real.log x) ^ (1 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hpow : (Real.log x) ^ (-(1 / 2 : ℝ)) * Real.log x =
      (Real.log x) ^ (1 / 2 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one (Real.log x)]
    rw [← Real.rpow_add hlog]
    norm_num
  rw [rpow_one_sub_eq_mul_exp x δ hx0]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  apply Real.exp_le_exp.mpr
  have hw := mul_le_mul_of_nonneg_right hwidth hlog.le
  rw [mul_assoc, hpow] at hw
  linarith

/-- Square-root exponential decay absorbs arbitrary real powers.
@isnad1 id=tendsto.1h2v.s6.54c8314167cd from=translated src=- shape=fd7f2fc8 vocab=1b4eb9c6
-/
theorem tendsto_rpow_mul_exp_neg_sqrt (A k : ℝ) (hk : 0 < k) :
    Tendsto (fun L : ℝ => L ^ A * Real.exp (-k * L ^ (1 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * A) k hk).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hL]
  congr 2
  ring

/--
@isnad1 id=eventual.1h2v.s6.8e81681bca12 from=translated src=- shape=c34dad78 vocab=018a73ae
-/
theorem eventually_mul_exp_neg_sqrt_le_rpow (A k : ℝ) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,
      L * Real.exp (-k * L ^ (1 / 2 : ℝ)) ≤ L ^ (-A) := by
  have he := (tendsto_rpow_mul_exp_neg_sqrt (A + 1) k hk).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have hp : 0 < L ^ (A + 1) := Real.rpow_pos_of_pos hL0 _
  have hb : Real.exp (-k * L ^ (1 / 2 : ℝ)) ≤ 1 / L ^ (A + 1) :=
    (le_div_iff₀ hp).mpr (by nlinarith)
  calc
    _ ≤ L * (1 / L ^ (A + 1)) := mul_le_mul_of_nonneg_left hb hL0.le
    _ = L ^ (-A) := by
      rw [one_div, ← Real.rpow_neg hL0.le]
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

/--
@isnad1 id=le.1h1v.s6.f2ffd7f0e6fc from=translated src=- shape=66a5aff7 vocab=6860bb9f
-/
theorem mangoldtMass_right_line_le (x : ℝ) (hx : 8 ≤ Real.log x) :
    mangoldtDirichletMass (1 + 1 / Real.log x) ≤ Real.log x + 40 := by
  have hl : 0 < Real.log x := by linarith
  have hc : 1 < 1 + 1 / Real.log x := by
    have hi : 0 < 1 / Real.log x := by positivity
    linarith
  have hcu : 1 + 1 / Real.log x ≤ 9 / 8 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hx
    linarith
  have h := mangoldtDirichletMass_le_pole_add_forty (1 + 1 / Real.log x) hc hcu
  simpa only [add_sub_cancel_left, one_div_one_div] using h

end TwinPrime.Analytic
