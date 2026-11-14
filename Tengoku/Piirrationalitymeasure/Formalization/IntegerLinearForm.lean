import Tengoku.Piirrationalitymeasure.Formalization.PolynomialTenClearing
import Tengoku.Piirrationalitymeasure.Formalization.IntegralDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The actual integer linear forms of Proposition 2.7, equations (2.35)--(2.37).
Both integer sequences are constructed and related to the original integral.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.0h1v.s6.7ff69676ae60 from=translated src=- shape=1ff63f6d vocab=94026fa3
-/
theorem normalizationMultiplier_eq_eight_common (n : ℕ) :
    normalizationMultiplier n = 8 * ((2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * reducedLcm n) := by
  unfold normalizationMultiplier
  rw [show 4 - 4645 * (n : ℤ) = 3 + (1 - 4645 * (n : ℤ)) by omega,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num
  ring

/--
@isnad1 id=ex.1h1v.s5.c85abc62d949 from=translated src=- shape=a503dbb7 vocab=fad682d8
-/
theorem normalizedPaperIntegral_integer_rationalCoefficient (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : ℤ, (normalizationMultiplier n : ℂ) * paperIntegral n =
      (U : ℂ) + (normalizedPiCoeff n : ℂ) * (Real.pi : ℂ) := by
  obtain ⟨P, hP⟩ := normalizedPolynomialIntegral_is_integer n hn
  obtain ⟨Q, hQ⟩ := normalizedNonlogPoleIntegral_is_integer n hn
  refine ⟨8 * (P + Q), ?_⟩
  have hpoly : (normalizationMultiplier n : ℂ) *
      (verticalPolynomialIntegralRat (polynomialPart n) : ℂ) =
        8 * normalizedPolynomialIntegral n := by
    rw [normalizationMultiplier_eq_eight_common, normalizedPolynomialIntegral,
      verticalPolynomial_integral_rat]
    push_cast
    ring
  have hpole : (normalizationMultiplier n : ℂ) * nonlogPoleIntegral n =
      8 * normalizedNonlogPoleIntegral n := by
    rw [normalizationMultiplier_eq_eight_common]
    unfold nonlogPoleIntegral normalizedNonlogPoleIntegral
    push_cast
    ring
  have hlog : (normalizationMultiplier n : ℂ) * (-laurentCoeffRat n 0 / 2 : ℚ) =
      (normalizedPiCoeff n : ℂ) := by
    unfold normalizedPiCoeff
    push_cast
    ring
  calc
    _ = (normalizationMultiplier n : ℂ) *
        (verticalPolynomialIntegralRat (polynomialPart n) : ℂ) +
      (normalizationMultiplier n : ℂ) * nonlogPoleIntegral n +
      ((normalizationMultiplier n : ℂ) * (-laurentCoeffRat n 0 / 2 : ℚ)) * (Real.pi : ℂ) := by
        rw [paperIntegral_decomposition]
        ring
    _ = _ := by
      rw [hpoly, hpole, hlog, hP, hQ]
      push_cast
      ring

/--
@isnad1 id=ex.1h1v.s7.cad5b40db876 from=translated src=- shape=2727c39c vocab=7d5c83ba
-/
theorem normalizedPaperIntegral_integerLinearForm (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ, (normalizationMultiplier n : ℂ) * paperIntegral n =
      (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
      (V : ℚ) = -(2 : ℚ) ^ (3 - 4645 * (n : ℤ)) * reducedLcm n * laurentCoeffRat n 0 := by
  obtain ⟨U, hU⟩ := normalizedPaperIntegral_integer_rationalCoefficient n hn
  obtain ⟨V, hV⟩ := normalizedPiCoeff_is_integer n hn
  refine ⟨U, V, ?_, ?_⟩
  · rw [hU, hV]
    push_cast
    rfl
  · rw [← hV, normalizedPiCoeff_formula]

noncomputable def integerCoeffU (n : ℕ) : ℤ :=
  if hn : 1 ≤ n then (normalizedPaperIntegral_integer_rationalCoefficient n hn).choose else 0

noncomputable def integerCoeffV (n : ℕ) : ℤ :=
  if hn : 1 ≤ n then (normalizedPiCoeff_is_integer n hn).choose else 0

/--
@isnad1 id=eq.1h1v.s4.c5eef0d9b8f1 from=translated src=- shape=2801aa92 vocab=43ef1155
-/
theorem integerCoeffV_cast (n : ℕ) (hn : 1 ≤ n) :
    (integerCoeffV n : ℚ) = normalizedPiCoeff n := by
  rw [integerCoeffV, dite_eq_left hn]
  exact (normalizedPiCoeff_is_integer n hn).choose_spec.symm

/--
@isnad1 id=eq.1h1v.s5.31cd0dd72348 from=translated src=- shape=5ea61068 vocab=cc1f7daa
-/
theorem paper_integerLinearForm (n : ℕ) (hn : 1 ≤ n) :
    (normalizationMultiplier n : ℂ) * paperIntegral n =
      (integerCoeffU n : ℂ) + (integerCoeffV n : ℂ) * (Real.pi : ℂ) := by
  have h := (normalizedPaperIntegral_integer_rationalCoefficient n hn).choose_spec
  rw [integerCoeffU, dite_eq_left hn]
  apply h.trans
  congr 1
  congr 1
  exact_mod_cast (integerCoeffV_cast n hn).symm

/--
@isnad1 id=eq.1h1v.s5.966c2729072d from=translated src=- shape=bc98ecdd vocab=731fd620
-/
theorem paper_real_integerLinearForm (n : ℕ) (hn : 1 ≤ n) :
    (normalizationMultiplier n : ℝ) * (paperIntegral n).re =
      (integerCoeffU n : ℝ) + (integerCoeffV n : ℝ) * Real.pi := by
  have h := congrArg Complex.re (paper_integerLinearForm n hn)
  simpa only [Complex.mul_re, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im,
    Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using h

end PiIrrationality
