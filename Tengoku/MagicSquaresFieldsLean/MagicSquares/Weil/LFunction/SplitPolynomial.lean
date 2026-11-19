import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.MonicWeights

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The sign from interchanging the two arguments of the split resultant.-/
noncomputable def splitWeightPhase {r : ℕ} (chars : Fin r → MulChar F ℂ) : ℂ :=
  ∏ i, chars i (-1)

/-- The resultant character weight in degree `n`. Keeping the degree
explicit makes the grading in the generating function transparent.-/
noncomputable def splitDegreeWeight {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (n : ℕ) (g : Polynomial F) : ℂ :=
  splitWeightPhase chars ^ n * splitEvaluationWeight roots chars g

omit [Fintype F] in
/--
@isnad1 id=eq.0h8v.s7.9e0a83309c63 from=translated src=- shape=e5e761d3 vocab=b6eee91e
-/
theorem splitDegreeWeight_mul {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (n k : ℕ) (g h : Polynomial F) :
    splitDegreeWeight roots chars (n + k) (g * h) =
      splitDegreeWeight roots chars n g * splitDegreeWeight roots chars k h := by
  simp only [splitDegreeWeight, pow_add, splitEvaluationWeight_mul]
  ring

/-- The coefficient obtained by summing the weights of all monic
polynomials of degree `n`.-/
noncomputable def splitLCoeff {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (n : ℕ) : ℂ :=
  ∑ v : Fin n → F, splitDegreeWeight roots chars n (monicOfCoeffs n v)

/--
@isnad1 id=eq.0h4v.s5.cd6d72a15b87 from=translated src=- shape=2f3a8c78 vocab=eaef35ec
-/
@[simp]
theorem splitLCoeff_zero {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) : splitLCoeff roots chars 0 = 1 := by
  simp [splitLCoeff, splitDegreeWeight]

/-- The degree-dependent resultant sign does not affect cancellation.
@isnad1 id=eq.3h5v.s7.8ddbebfee23f from=translated src=- shape=ada2ba06 vocab=fab6a4dc
-/
theorem splitLCoeff_eq_zero {r n : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) (hn : r ≤ n) : splitLCoeff roots chars n = 0 := by
  simp only [splitLCoeff, splitDegreeWeight, ← Finset.mul_sum,
    sum_splitEvaluationWeight_monic_eq_zero roots hinj chars hn hchars, mul_zero]

/-- The coefficient of `T` is the original character sum, including the
resultant sign. This fixes the sign convention in the future power-sum
identity `S_s = -∑ alpha_j^s`.
@isnad1 id=eq.0h4v.s7.6b8a7d6ae241 from=translated src=- shape=35bba98d vocab=78d8cd2e
-/
theorem splitLCoeff_one {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) :
    splitLCoeff roots chars 1 = ∑ t : F, ∏ i, chars i (t - roots i) := by
  classical
  have hlinear (v : Fin 1 → F) :
      splitDegreeWeight roots chars 1 (monicOfCoeffs 1 v) =
        ∏ i, chars i (-(v 0) - roots i) := by
    simp only [splitDegreeWeight, pow_one, splitEvaluationWeight, monicOfCoeffs_one,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      splitWeightPhase, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← map_mul]
    congr 1
    ring
  simp only [splitLCoeff, hlinear]
  let e : (Fin 1 → F) ≃ F := (Equiv.funUnique (Fin 1) F).trans (Equiv.neg F)
  exact e.sum_comp (fun t => ∏ i, chars i (t - roots i))

/-- The finite L-polynomial in the split case of LN97 Theorem 5.39.
The coefficient-cancellation theorem proves that truncation at `r` loses
no terms from the monic-polynomial generating series.-/
noncomputable def splitLPolynomial {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range r, Polynomial.monomial n (splitLCoeff roots chars n)

/--
@isnad1 id=eq.2h5v.s7.afb77a9d1850 from=translated src=- shape=12214129 vocab=da7a6b9b
-/
theorem splitLPolynomial_coeff {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) (n : ℕ) :
    (splitLPolynomial roots chars).coeff n = splitLCoeff roots chars n := by
  classical
  simp only [splitLPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < r
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      simp [hbn]
    · intro h
      exact (h (Finset.mem_range.mpr hn)).elim
  · rw [splitLCoeff_eq_zero roots hinj chars hchars (by omega)]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by have := Finset.mem_range.mp hb; omega
    simp [hbn]

/--
@isnad1 id=lt.0h4v.s5.1e61f28bea7e from=translated src=- shape=81992a58 vocab=54a03941
-/
theorem splitLPolynomial_degree_lt {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) : (splitLPolynomial roots chars).degree < r := by
  apply Polynomial.mem_degreeLT.mp
  apply (Polynomial.degreeLT ℂ r).sum_mem
  intro n hn
  apply Polynomial.mem_degreeLT.mpr
  exact (Polynomial.degree_monomial_le _ _).trans_lt
    (by exact_mod_cast Finset.mem_range.mp hn)

/--
@isnad1 id=eq.2h4v.s7.80acdc7e7734 from=translated src=- shape=bd3b62f4 vocab=b4adb611
-/
theorem splitLPolynomial_coeff_zero {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) : (splitLPolynomial roots chars).coeff 0 = 1 := by
  rw [splitLPolynomial_coeff roots hinj chars hchars, splitLCoeff_zero]

/--
@isnad1 id=ne.2h4v.s7.b33867ac350d from=translated src=- shape=fd3bc4e7 vocab=7b23eee8
-/
theorem splitLPolynomial_ne_zero {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) : splitLPolynomial roots chars ≠ 0 := by
  intro h
  have hc := splitLPolynomial_coeff_zero roots hinj chars hchars
  simp [h] at hc

/-- The L-polynomial has degree at most `r-1`, the number of complex
numbers required for the sharp Weil constant.
@isnad1 id=le.2h4v.s7.c762e836c6a9 from=translated src=- shape=6e48c706 vocab=b6297188
-/
theorem splitLPolynomial_natDegree_le {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) : (splitLPolynomial roots chars).natDegree ≤ r - 1 := by
  have h := splitLPolynomial_degree_lt roots chars
  rw [Polynomial.degree_eq_natDegree (splitLPolynomial_ne_zero roots hinj chars hchars)] at h
  have hn : (splitLPolynomial roots chars).natDegree < r := by exact_mod_cast h
  omega

end MagicSquares.LN97
