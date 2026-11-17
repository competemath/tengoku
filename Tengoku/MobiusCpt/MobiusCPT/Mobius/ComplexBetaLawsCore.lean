import Tengoku.MobiusCpt.MobiusCPT.Analysis.Strip
import Tengoku.MobiusCpt.MobiusCPT.Mobius.Beta
import Tengoku.MobiusCpt.MobiusCPT.Mobius.ComplexBeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complex boost at real parameters and at `τ = iπ`

[T26], equations (3.4)-(3.5) and Lemma 3.7.  This file records the pointwise facts about the
complex boost at the two distinguished parameter values that the source singles out: the real
boundary line of the strip, where the complex expression must reproduce the ordinary conformal
action `β_d(v_t)`, and the upper boundary point `τ = iπ`, where the boost is inversion.  Nothing
here depends on the test-function packaging of the boost.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-! ### Real parameters -/

/-- [T26], eq. (3.5); for a real boost parameter the conformal scalar
`cosh t + Re(z) sinh t` is strictly positive on the circle: `cosh` dominates `|sinh|`, and
`|Re z| ≤ 1`.
@isnad1 id=lt.0h2v.s6.d3890230f089 from=translated src=- shape=c518f2f4 vocab=fe3e233e
-/
theorem cosh_add_re_mul_sinh_pos (t : ℝ) (z : Circle) :
    0 < Real.cosh t + (z : ℂ).re * Real.sinh t := by
  have hre : |(z : ℂ).re| ≤ 1 := by
    have h := Complex.abs_re_le_norm (z : ℂ)
    rwa [Circle.norm_coe] at h
  have hcosh : 0 < Real.cosh t := Real.cosh_pos t
  have hsq : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
  have habs : |Real.sinh t| < Real.cosh t := by
    nlinarith [sq_abs (Real.sinh t), abs_nonneg (Real.sinh t), hcosh, hsq]
  have hbound : |(z : ℂ).re * Real.sinh t| ≤ |Real.sinh t| := by
    rw [abs_mul]
    calc
      |(z : ℂ).re| * |Real.sinh t| ≤ 1 * |Real.sinh t| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg _)
      _ = |Real.sinh t| := one_mul _
  have hneg : -|(z : ℂ).re * Real.sinh t| ≤ (z : ℂ).re * Real.sinh t := neg_abs_le _
  linarith

/-- [T26], eq. (3.4); for a real boost parameter the denominator of `v_{-t}` never vanishes on the
circle, so the complex boost has no pole on the real boundary line of the strip.
@isnad1 id=ne.0h2v.s6.88cd7902e4f4 from=translated src=- shape=f0affb9b vocab=55fd2ca6
-/
theorem cden_neg_ofReal_ne_zero (t : ℝ) (z : Circle) : cden (-(t : ℂ)) z ≠ 0 := by
  intro h
  have hnormSq := normSq_cden_neg_ofReal t z
  rw [h, map_zero] at hnormSq
  exact absurd hnormSq.symm (ne_of_gt (cosh_add_re_mul_sinh_pos t z))

/-- [T26], §3; at a real parameter the sphere-valued boost is the ordinary circle action of the
real boost `v_{-t}`.
@isnad1 id=eq.0h2v.s6.c6c487397a89 from=translated src=- shape=7cee75ce vocab=b1adced7
-/
theorem vApplyNegSphere_ofReal (t : ℝ) (z : Circle) :
    vApplyNegSphere (t : ℂ) z = (((boostMat (-t) • z : Circle) : ℂ) : OnePoint ℂ) := by
  have hden : cden (-(t : ℂ)) z ≠ 0 := cden_neg_ofReal_ne_zero t z
  rw [vApplyNegSphere, ite_eq_right hden]
  congr 1
  rw [coe_boostMat_smul (-t) z, vApply]
  congr 2 <;> rw [Complex.ofReal_neg]

/-- [T26], eq. (3.5); at a real parameter the complex conformal scalar is the real one.
@isnad1 id=eq.0h2v.s7.5256840b51b4 from=translated src=- shape=5c999e95 vocab=68705e81
-/
theorem cosh_add_re_mul_sinh_ofReal (t : ℝ) (z : Circle) :
    Complex.cosh (t : ℂ) + ((z : ℂ).re : ℂ) * Complex.sinh (t : ℂ) =
      ((Real.cosh t + (z : ℂ).re * Real.sinh t : ℝ) : ℂ) := by
  rw [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.ofReal_add, Complex.ofReal_mul]

/-- [T26], Definition 3.1; a real parameter lies on the boundary of the closed strip.
@isnad1 id=mem.0h1v.s4.a282009bc1da from=translated src=- shape=de898299 vocab=161c21f0
-/
theorem ofReal_mem_strip_I_mul_pi (t : ℝ) :
    (t : ℂ) ∈ strip (Complex.I * Real.pi) :=
  ofReal_mem_strip _ t

/-! ### The parameter `τ = iπ` -/

/-- [T26], Lemma 3.7; the numerator of `v_{-iπ}` is the imaginary unit.
@isnad1 id=eq.0h1v.s6.173989618a70 from=translated src=- shape=24438c2a vocab=5ef57106
-/
theorem cnum_neg_I_mul_pi (z : Circle) :
    cnum (-(Complex.I * Real.pi)) z = Complex.I := by
  rw [cnum_neg, cosh_I_mul_pi_div_two, sinh_I_mul_pi_div_two, zero_mul, zero_add]

/-- [T26], Lemma 3.7; the denominator of `v_{-iπ}` is `i z`, which never vanishes on the
circle.
@isnad1 id=eq.0h1v.s7.1bcce99f9066 from=translated src=- shape=beea044f vocab=8a036945
-/
theorem cden_neg_I_mul_pi (z : Circle) :
    cden (-(Complex.I * Real.pi)) z = Complex.I * (z : ℂ) := by
  rw [cden_neg, cosh_I_mul_pi_div_two, sinh_I_mul_pi_div_two, add_zero]

/-- [T26], Lemma 3.7; the denominator of `v_{-iπ}` does not vanish on the circle.
@isnad1 id=ne.0h1v.s6.8ed1211ab954 from=translated src=- shape=d9d554dd vocab=8a036945
-/
theorem cden_neg_I_mul_pi_ne_zero (z : Circle) :
    cden (-(Complex.I * Real.pi)) z ≠ 0 := by
  rw [cden_neg_I_mul_pi]
  exact mul_ne_zero Complex.I_ne_zero (Circle.coe_ne_zero z)

/-- [T26], Lemma 3.7; `v_{-iπ}·z = z⁻¹`, so at the upper boundary point of the strip the complex
boost is inversion.
@isnad1 id=eq.0h1v.s6.f2651d76160d from=translated src=- shape=bcd1e844 vocab=87ccb094
-/
theorem vApplyNegSphere_I_mul_pi (z : Circle) :
    vApplyNegSphere (Complex.I * Real.pi) z = (((z : ℂ)⁻¹ : ℂ) : OnePoint ℂ) := by
  have hden : cden (-(Complex.I * Real.pi)) z ≠ 0 := cden_neg_I_mul_pi_ne_zero z
  rw [vApplyNegSphere, ite_eq_right hden, cnum_neg_I_mul_pi, cden_neg_I_mul_pi]
  congr 1
  field_simp

/-- [T26], Lemma 3.7; `cosh (iπ) = -1`.
@isnad1 id=eq.0h0v.s4.d62e7312a719 from=translated src=- shape=8ffd0f4f vocab=3a30959c
-/
theorem cosh_I_mul_pi : Complex.cosh (Complex.I * Real.pi) = -1 := by
  rw [show Complex.I * (Real.pi : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I by ring,
    Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_pi]
  norm_num

/-- [T26], Lemma 3.7; `sinh (iπ) = 0`.
@isnad1 id=eq.0h0v.s4.b0628590c5dc from=translated src=- shape=f7010451 vocab=d936860e
-/
theorem sinh_I_mul_pi : Complex.sinh (Complex.I * Real.pi) = 0 := by
  rw [show Complex.I * (Real.pi : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I by ring,
    Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_pi]
  norm_num

/-- [T26], Lemma 3.7; at `τ = iπ` the conformal scalar of eq. (3.5) is `-1` for every point of the
circle.
@isnad1 id=eq.0h1v.s6.9069ca6971f7 from=translated src=- shape=32914c52 vocab=e8e908e1
-/
theorem cosh_add_re_mul_sinh_I_mul_pi (z : Circle) :
    Complex.cosh (Complex.I * Real.pi) +
        ((z : ℂ).re : ℂ) * Complex.sinh (Complex.I * Real.pi) = -1 := by
  rw [cosh_I_mul_pi, sinh_I_mul_pi, mul_zero, add_zero]

/-- [T26], Definition 3.5, equation (3.4); the source sign `(-1)^{d-1}` at `τ = iπ` is
`(-1)^{d+1}` for `d : ℕ`, since the two exponents have the same parity in `ℂ`.  This is the
identification the Issue #2 statement contract records.
@isnad1 id=eq.0h1v.s6.55f8c68c0ae3 from=translated src=- shape=76a47869 vocab=70d7568d
-/
theorem neg_one_zpow_sub_one (d : ℕ) :
    (-1 : ℂ) ^ ((d : ℤ) - 1) = (-1 : ℂ) ^ (d + 1) := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [zpow_sub_one₀ hne, zpow_natCast, pow_succ]
  norm_num

/-- [T26], Definition 3.1; `iπ` lies in its own closed strip.
@isnad1 id=mem.0h0v.s4.77972381815d from=translated src=- shape=bedc945a vocab=1c157ae4
-/
theorem I_mul_pi_mem_strip : (Complex.I * Real.pi) ∈ strip (Complex.I * Real.pi) := by
  rw [mem_strip]
  exact ⟨min_le_right _ _, le_max_right _ _⟩

end

end MobiusCPT
