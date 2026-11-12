import Tengoku.AbelFormalization.AbelFormalization.AbelDensityExtension
import Tengoku.Seed.Analysis.Complex.SummableUniformlyOn
import Tengoku.Seed.Analysis.Normed.Group.FunctionSeries
import Tengoku.Seed.Analysis.PSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Summing the logarithmic defect of an Abel density

The density is obtained by exponentiating a normally convergent series along
the contracting logarithmic orbit.  The quadratic defect and inverse-linear
orbit estimates make the majorant a convergent square-reciprocal series.
-/

noncomputable section

namespace AbelFormalization

open Set Filter Function
open scoped Topology

def logDensitySum (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, h (complexL^[n] z)

def densityFromLogDefect (h : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.exp (logDensitySum h (x : ℂ)).re / x ^ 2

/--
@isnad1 id=summable.0h1v.s5.64ff2e3e606b from=translated src=- shape=4b6b1d1b vocab=72262d31
-/
theorem summable_square_reciprocal_majorant (K : ℝ) :
    Summable (fun n : ℕ => K / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h.mul_left K

/--
@isnad1 id=summable.1h3v.s6.c0f4fe156ad2 from=translated src=- shape=1b43c4e1 vocab=d87c3c23
-/
theorem summable_logDensityTerms_of_bound {h : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (hbound : ∀ n : ℕ, ‖h (complexL^[n] z)‖ ≤ K / ((n : ℝ) + 1) ^ 2) :
    Summable (fun n : ℕ => h (complexL^[n] z)) :=
  (summable_square_reciprocal_majorant K).of_norm_bounded hbound

/--
@isnad1 id=analytic.3h3v.s7.b4c75621b659 from=translated src=- shape=5abd1410 vocab=f5643506
-/
theorem analyticOnNhd_logDensitySum_of_bound {h : ℂ → ℂ} {s : Set ℂ} {K : ℝ}
    (hs : IsOpen s)
    (ha : ∀ n : ℕ, AnalyticOnNhd ℂ (fun z => h (complexL^[n] z)) s)
    (hbound : ∀ n : ℕ, ∀ z ∈ s, ‖h (complexL^[n] z)‖ ≤ K / ((n : ℝ) + 1) ^ 2) :
    AnalyticOnNhd ℂ (logDensitySum h) s := by
  have hu : SummableUniformlyOn (fun n : ℕ => fun z => h (complexL^[n] z)) s :=
    ⟨_, hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
      (tendstoUniformlyOn_tsum (summable_square_reciprocal_majorant K) hbound)⟩
  exact (hu.hasSumUniformlyOn.hasSumLocallyUniformlyOn.summableLocallyUniformlyOn
    |>.differentiableOn hs (fun n z hz => (ha n z hz).differentiableAt)).analyticOnNhd hs

/--
@isnad1 id=lt.1h2v.s4.716d4884f666 from=translated src=- shape=271d35e4 vocab=b432efad
-/
theorem densityFromLogDefect_pos (h : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    0 < densityFromLogDefect h x :=
  div_pos (Real.exp_pos _) (sq_pos_of_pos hx)

/--
@isnad1 id=analytic.2h2v.s6.20e6f20b357a from=translated src=- shape=01248565 vocab=6f3147d7
-/
theorem analyticAt_densityFromLogDefect {h : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (ha : AnalyticAt ℂ (logDensitySum h) (x : ℂ)) :
    AnalyticAt ℝ (densityFromLogDefect h) x := by
  exact ha.re_ofReal.rexp.div (analyticAt_id.pow 2) (pow_ne_zero _ (ne_of_gt hx))

/--
@isnad1 id=eq.3h2v.s7.ef931301b498 from=translated src=- shape=43a615a8 vocab=24dc4e61
-/
theorem densityFromLogDefect_invariant {h : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : Summable (fun n : ℕ => h (complexL^[n] (x : ℂ))))
    (he : (h (x : ℂ)).re = Real.log (x ^ 2 / ((1 + x) * (L x) ^ 2))) :
    densityFromLogDefect h (L x) / (1 + x) = densityFromLogDefect h x := by
  have hsum : logDensitySum h (x : ℂ) = h (x : ℂ) + logDensitySum h (L x : ℂ) := by
    rw [logDensitySum, hs.tsum_eq_zero_add]
    simp only [Function.iterate_zero, id_eq, logDensitySum,
      Function.iterate_succ_apply, complexL_ofReal (by linarith : 0 ≤ 1 + x)]
  have hp : 0 < x ^ 2 / ((1 + x) * (L x) ^ 2) :=
    div_pos (sq_pos_of_pos hx) (mul_pos (by linarith) (sq_pos_of_pos (L_pos hx)))
  unfold densityFromLogDefect
  rw [hsum, Complex.add_re, he, Real.exp_add, Real.exp_log hp]
  have hadd : 1 + x ≠ 0 := by linarith
  field_simp [ne_of_gt hx, ne_of_gt (L_pos hx), hadd]

end AbelFormalization
