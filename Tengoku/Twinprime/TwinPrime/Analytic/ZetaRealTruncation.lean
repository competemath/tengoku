import Tengoku.Twinprime.TwinPrime.Analytic.ZetaContinuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real zeta truncation below one

The pole contribution to the finite sum minus zeta has the positive
denominator `1 - β`. The error is at most `N^(-β)` for `0 < β < 1`.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The main term in a finite real zeta sum below one has positive sign.
@isnad1 id=le.3h2v.s7.4a17f214280b from=translated src=- shape=53873c13 vocab=6933fbd5
-/
theorem norm_zeta_real_sum_sub_zeta_sub_main_le (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ‖(∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ) -
        (N : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ))‖ ≤ (N : ℝ) ^ (-β) := by
  have h := norm_riemannZeta_sub_sum_sub_pole_le_of_re_pos N hN (β : ℂ)
    (by simpa only [Complex.ofReal_re] using hβ0)
    (by exact_mod_cast (ne_of_lt hβ1))
  have heq : riemannZeta (β : ℂ) -
      (∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-(β : ℂ))) -
        (N : ℂ) ^ (1 - (β : ℂ)) / ((β : ℂ) - 1) =
      -((∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ) -
        (N : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ))) := by
    rw [show (β : ℂ) - 1 = -(1 - (β : ℂ)) by ring, div_neg]
    ring
  rw [heq, norm_neg] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0,
    Complex.ofReal_re, div_self hβ0.ne', one_mul] using h

/--
@isnad1 id=eq.2h2v.s7.481c6b432a5d from=translated src=- shape=68765aae vocab=2e22d545
-/
theorem norm_zeta_real_pole_term (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ1 : β < 1) :
    ‖(N : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ))‖ =
      (N : ℝ) ^ (1 - β) / (1 - β) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [norm_div, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  rw [show (1 : ℂ) - (β : ℂ) = ((1 - β : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hβ1)]

/-- A convenient bound for the full finite sum minus zeta, with no
unproved approximation premise.
@isnad1 id=le.3h2v.s7.7267aa1397a0 from=translated src=- shape=e24f53a3 vocab=1e48aaa6
-/
theorem norm_zeta_real_sum_sub_zeta_le (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ‖(∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ)‖ ≤
      2 * (N : ℝ) ^ (1 - β) / (1 - β) := by
  have herr := norm_zeta_real_sum_sub_zeta_sub_main_le N hN β hβ0 hβ1
  have hmain := norm_zeta_real_pole_term N hN β hβ1
  have hpow : (N : ℝ) ^ (-β) ≤ (N : ℝ) ^ (1 - β) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  have hfrac : (N : ℝ) ^ (1 - β) ≤ (N : ℝ) ^ (1 - β) / (1 - β) := by
    apply (le_div_iff₀ (sub_pos.mpr hβ1)).mpr
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by linarith)
  have hn := norm_add_le
    ((∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ) -
      (N : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ)))
    ((N : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ)))
  rw [sub_add_cancel, hmain] at hn
  calc
    _ ≤ (N : ℝ) ^ (-β) + (N : ℝ) ^ (1 - β) / (1 - β) := hn.trans (add_le_add herr le_rfl)
    _ ≤ (N : ℝ) ^ (1 - β) / (1 - β) + (N : ℝ) ^ (1 - β) / (1 - β) :=
      add_le_add (hpow.trans hfrac) le_rfl
    _ = _ := by ring

end TwinPrime.Analytic
