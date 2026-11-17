import Tengoku.Seed.Analysis.RCLike.Sqrt
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Complex_sqrt_mul_sqrt_eq_of_re_pos.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Complex_sqrt_mul_sqrt_eq_of_re_pos

set_option autoImplicit false

noncomputable section

open Complex

open scoped Real

namespace DedekindEtaLaw

/--
@isnad1 id=eq.0h1v.s4.24ab7fd8c012 from=translated src=- shape=6cd42883 vocab=38fbebb9
-/
lemma sqrt_sq (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  have h := cpow_nat_inv_pow a two_ne_zero
  rw [Complex.sqrt]
  norm_num at h ⊢
  exact h

/--
@isnad1 id=eq.0h1v.s5.f413c23b74b2 from=translated src=- shape=5d265ca5 vocab=7db86fe2
-/
lemma sqrt_re (a : ℂ) : (Complex.sqrt a).re = √((‖a‖ + a.re) / 2) := by
  rw [Complex.sqrt]; exact cpow_inv_two_re a

/--
@isnad1 id=eq.0h1v.s5.bed81469912d from=translated src=- shape=00b27188 vocab=8c804cdc
-/
lemma abs_sqrt_im (a : ℂ) : |(Complex.sqrt a).im| = √((‖a‖ - a.re) / 2) := by
  rw [Complex.sqrt]; exact abs_cpow_inv_two_im a

/--
@isnad1 id=lt.1h1v.s4.4757509510ee from=translated src=- shape=1fdb91b8 vocab=d948c70a
-/
lemma abs_sqrt_im_lt_re {a : ℂ} (ha : 0 < a.re) : |(Complex.sqrt a).im| < (Complex.sqrt a).re := by
  rw [sqrt_re, abs_sqrt_im]
  apply Real.sqrt_lt_sqrt
  · have := re_le_norm a
    linarith
  · linarith

lemma eq_of_sq_eq_sq_of_re_pos {s t : ℂ} (h : s ^ 2 = t ^ 2) (hs : 0 < s.re) (ht : 0 < t.re) :
    s = t := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · exfalso
    rw [h, neg_re] at hs
    linarith

/--
@isnad1 id=lt.1h1v.s5.5f1f95794e51 from=translated src=- shape=b1ba0b72 vocab=09103047
-/
lemma sqrt_neg_I_mul_re_pos {x : ℂ} (hx : |x.im| < x.re) : 0 < (Complex.sqrt (-I) * x).re := by
  rw [Complex.sqrt_neg_I, mul_assoc, re_ofReal_mul]
  have h2 : (0 : ℝ) < √(2⁻¹) := Real.sqrt_pos_of_pos (by norm_num)
  have : ((1 - I) * x).re = x.re + x.im := by simp [mul_re, sub_re, sub_im]
  rw [this]
  exact mul_pos h2 (by cases abs_lt.1 hx; linarith)

/--
@isnad1 id=eq.4h3v.s6.422266e7414f from=translated src=- shape=39558d98 vocab=7fe8133a
-/
theorem sqrt_mul_sqrt_eq {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re)
    (h : u * v = -I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-I) * Complex.sqrt w := by
  apply eq_of_sq_eq_sq_of_re_pos
  · rw [mul_pow, mul_pow, sqrt_sq, sqrt_sq, sqrt_sq, sqrt_sq, h]
  · have h1 := abs_sqrt_im_lt_re hu
    have h2 := abs_sqrt_im_lt_re hv
    rw [mul_re]
    have : |(Complex.sqrt u).im * (Complex.sqrt v).im| < (Complex.sqrt u).re * (Complex.sqrt v).re := by
      rw [abs_mul]
      exact mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)
    have := (abs_lt.1 this).2
    linarith [(abs_lt.1 ‹|(Complex.sqrt u).im * (Complex.sqrt v).im| < _›).1]
  · exact sqrt_neg_I_mul_re_pos (abs_sqrt_im_lt_re hw)

end DedekindEtaLaw

end

/--
@isnad1 id=eq.4h3v.s6.422266e7414f from=translated src=- shape=39558d98 vocab=7fe8133a
-/
theorem solution {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-Complex.I) * Complex.sqrt w :=
  DedekindEtaLaw.sqrt_mul_sqrt_eq hu hv hw h
