import Tengoku.Piirrationalitymeasure.Formalization.PartialFractionIdentity
import Tengoku.Piirrationalitymeasure.Formalization.PolynomialIntegral
import Tengoku.Piirrationalitymeasure.Formalization.LogarithmicIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The actual integral `J_n` and its rational linear form (2.4).
The two factors of `I`, from the paper and the vertical parametrization,
account for the minus sign in the real interval integral.
-/

namespace PiIrrationality

open Polynomial

noncomputable def verticalDensity (n : ℕ) (s : ℝ) : ℂ :=
  5 * verticalSegment s ^ (2 * 1857 * n) *
    (verticalSegment s ^ 4 + 6 * verticalSegment s ^ 2 + 25) ^ (3714 * n) /
      (25 - verticalSegment s ^ 2) ^ (5570 * n + 1)

noncomputable def paperIntegral (n : ℕ) : ℂ :=
  -(∫ s : ℝ in (-2)..2, verticalDensity n s)

noncomputable def nonlogPoleIntegral (n : ℕ) : ℂ :=
  -(∫ s : ℝ in (-2)..2,
    ∑ j ∈ Finset.Icc 1 (5570 * n), (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s)

theorem polePair_eq_nat (j : ℕ) (s : ℝ) :
    polePair j s =
      1 / (5 + verticalSegment s) ^ (j + 1) +
        1 / (5 - verticalSegment s) ^ (j + 1) := by
  have he : -(j : ℤ) - 1 = -((j + 1 : ℕ) : ℤ) := by omega
  have hl : 5 + verticalSegment s = 4 + (s : ℂ) * Complex.I := by
    unfold verticalSegment
    ring
  have hr : 5 - verticalSegment s = 6 - (s : ℂ) * Complex.I := by
    unfold verticalSegment
    ring
  simp only [polePair, he, zpow_neg, zpow_natCast, hl, hr, one_div]

theorem verticalDensity_partialFractions (n : ℕ) (s : ℝ) :
    verticalDensity n s = aeval (verticalSegment s) (polynomialPart n) +
      (laurentCoeffRat n 0 : ℂ) * polePair 0 s +
        ∑ j ∈ Finset.Icc 1 (5570 * n), (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s := by
  have hleft : verticalSegment s + 5 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [verticalSegment] at this
  have hright : verticalSegment s - 5 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [verticalSegment] at this
  rw [verticalDensity, rationalFunction_partialFractions n _ hleft hright]
  simp_rw [← polePair_eq_nat]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s)]
  have hrange : Finset.range (5570 * n + 1) = insert 0 (Finset.Icc 1 (5570 * n)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero]
  ring

theorem nonlogPoleIntegrand_continuous (n : ℕ) :
    Continuous (fun s : ℝ =>
      ∑ j ∈ Finset.Icc 1 (5570 * n), (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s) := by
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (polePair_continuous j)

theorem verticalDensity_continuous (n : ℕ) : Continuous (verticalDensity n) := by
  have hfun : verticalDensity n = fun s =>
      aeval (verticalSegment s) (polynomialPart n) +
        (laurentCoeffRat n 0 : ℂ) * polePair 0 s +
          ∑ j ∈ Finset.Icc 1 (5570 * n), (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s :=
    funext (verticalDensity_partialFractions n)
  rw [hfun]
  exact (((polynomialPart n).continuous_aeval.comp verticalSegment_continuous).add
    (continuous_const.mul (polePair_continuous 0))).add (nonlogPoleIntegrand_continuous n)

theorem paperIntegral_decomposition (n : ℕ) :
    paperIntegral n = (verticalPolynomialIntegralRat (polynomialPart n) : ℂ) +
      nonlogPoleIntegral n + (-laurentCoeffRat n 0 / 2 : ℚ) * (Real.pi : ℂ) := by
  have hp := ((polynomialPart n).continuous_aeval.comp
    verticalSegment_continuous).intervalIntegrable (μ := MeasureTheory.volume) (-2) 2
  have hlog := ((continuous_const (y := (laurentCoeffRat n 0 : ℂ))).mul
    (polePair_continuous 0)).intervalIntegrable (μ := MeasureTheory.volume) (-2) 2
  have hnonlog := (nonlogPoleIntegrand_continuous n).intervalIntegrable
    (μ := MeasureTheory.volume) (-2) 2
  dsimp only [Function.comp_def, Pi.mul_apply] at hp hlog
  change IntervalIntegrable (fun s : ℝ => (laurentCoeffRat n 0 : ℂ) * polePair 0 s)
    MeasureTheory.volume (-2) 2 at hlog
  unfold paperIntegral
  simp_rw [verticalDensity_partialFractions]
  rw [intervalIntegral.integral_add (hp.add hlog) hnonlog,
    intervalIntegral.integral_add hp hlog]
  have hP := verticalPolynomial_integral_rat (polynomialPart n)
  have hL := logarithmicCoeff_integral n
  unfold nonlogPoleIntegral
  linear_combination hP + hL

theorem nonlogPoleIntegral_is_rational (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℚ, nonlogPoleIntegral n = (q : ℂ) := by
  obtain ⟨z, hz⟩ := normalizedNonlogPoleIntegral_is_integer n hn
  let A : ℚ := (2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * reducedLcm n
  have hA : A ≠ 0 := by
    dsimp [A]
    apply mul_ne_zero (zpow_ne_zero _ (by norm_num))
    rw [reducedLcm_eq_natCast]
    exact_mod_cast (reducedLcmNat_pos n hn).ne'
  have hAC : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  refine ⟨(z : ℚ) / A, ?_⟩
  have hprod : (A : ℂ) * nonlogPoleIntegral n = (z : ℂ) := by
    simpa only [A, nonlogPoleIntegral, normalizedNonlogPoleIntegral,
      mul_neg, neg_mul] using hz
  apply (mul_left_cancel₀ hAC)
  rw [hprod]
  push_cast
  field_simp

theorem paperIntegral_rational_linearForm (n : ℕ) (hn : 1 ≤ n) :
    ∃ u : ℚ, paperIntegral n = (u : ℂ) +
      (-laurentCoeffRat n 0 / 2 : ℚ) * (Real.pi : ℂ) := by
  obtain ⟨q, hq⟩ := nonlogPoleIntegral_is_rational n hn
  refine ⟨verticalPolynomialIntegralRat (polynomialPart n) + q, ?_⟩
  rw [paperIntegral_decomposition, hq]
  push_cast
  rfl

end PiIrrationality
