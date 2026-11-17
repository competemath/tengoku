import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Complex_log_add_log_eq_log_sub_of_re_pos.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Complex_log_add_log_eq_log_sub_of_re_pos

set_option autoImplicit false

noncomputable section

open Complex

open scoped Real

namespace DedekindEtaLog

/--
@isnad1 id=eq.5h2v.s5.1888d4a0cfd8 from=translated src=- shape=7032fc57 vocab=5ddfe85e
-/
lemma exp_inj_of_im {x y : ℂ} (hx1 : -π < x.im) (hx2 : x.im ≤ π) (hy1 : -π < y.im) (hy2 : y.im ≤ π)
    (h : exp x = exp y) : x = y := by
  rw [← log_exp hx1 hx2, ← log_exp hy1 hy2, h]

/--
@isnad1 id=and.1h1v.s6.3a39fb41ac27 from=translated src=- shape=6dba8754 vocab=2d5e91d6
-/
lemma arg_mem_of_re_pos {u : ℂ} (hu : 0 < u.re) : -(π / 2) < arg u ∧ arg u < π / 2 :=
  abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hu))

/--
@isnad1 id=eq.4h3v.s6.4099757e88d3 from=translated src=- shape=a84c53f5 vocab=26814477
-/
theorem log_add_log_eq {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re)
    (h : u * v = -I * w) : log u + log v = log w - π * I / 2 := by
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hv0 : v ≠ 0 := fun h0 => by simp [h0] at hv
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  obtain ⟨hu1, hu2⟩ := arg_mem_of_re_pos hu
  obtain ⟨hv1, hv2⟩ := arg_mem_of_re_pos hv
  obtain ⟨hw1, hw2⟩ := arg_mem_of_re_pos hw
  have hpi := Real.pi_pos
  refine exp_inj_of_im ?_ ?_ ?_ ?_ ?_
  · simp only [add_im, log_im]; linarith
  · simp only [add_im, log_im]; linarith
  · simp only [sub_im, log_im, div_ofNat_im, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re]; linarith
  · simp only [sub_im, log_im, div_ofNat_im, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re]; linarith
  · rw [exp_add, exp_log hu0, exp_log hv0, exp_sub, exp_log hw0, h,
      show π * I / 2 = (π / 2 : ℂ) * I by ring, exp_mul_I]
    have hc : Complex.cos (π / 2 : ℂ) = 0 := by exact_mod_cast Complex.cos_pi_div_two
    have hs : Complex.sin (π / 2 : ℂ) = 1 := by exact_mod_cast Complex.sin_pi_div_two
    rw [hc, hs]
    field_simp
    ring_nf
    simp

end DedekindEtaLog

end

/--
@isnad1 id=eq.4h3v.s6.4099757e88d3 from=translated src=- shape=a84c53f5 vocab=26814477
-/
theorem solution {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.log u + Complex.log v = Complex.log w - Real.pi * Complex.I / 2 :=
  DedekindEtaLog.log_add_log_eq hu hv hw h
