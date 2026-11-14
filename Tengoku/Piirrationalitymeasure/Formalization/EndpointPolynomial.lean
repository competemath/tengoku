import Tengoku.Piirrationalitymeasure.Formalization.PolynomialIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The Gaussian-integer endpoint coefficients in (2.23) and the termwise
endpoint integral (2.27). The divisibility estimate (2.24) is separate.
-/

namespace PiIrrationality

open Polynomial

def lowerEndpointGI : GI := ⟨-1, -2⟩

theorem lowerEndpointGI_cast : (lowerEndpointGI : ℂ) = -1 - 2 * Complex.I := by
  simp [lowerEndpointGI, GaussianInt.toComplex_def']
  ring

noncomputable def endpointPolynomial (n : ℕ) : Polynomial GI :=
  taylor lowerEndpointGI ((polynomialPart n).map (Int.castRingHom GI))

noncomputable def endpointCoeff (n k : ℕ) : GI := (endpointPolynomial n).coeff k

theorem endpointPolynomial_natDegree (n : ℕ) :
    (endpointPolynomial n).natDegree = 7430 * n - 2 := by
  rw [endpointPolynomial, natDegree_taylor,
    natDegree_map_eq_of_injective (f := Int.castRingHom GI) Int.cast_injective,
    polynomialPart_natDegree]

theorem endpointPolynomial_eval (n : ℕ) (t : ℂ) :
    (endpointPolynomial n).eval₂ GaussianInt.toComplex (t - (lowerEndpointGI : ℂ)) =
      aeval t (polynomialPart n) := by
  unfold endpointPolynomial
  rw [taylor_apply, eval₂_comp]
  simp only [eval₂_add, eval₂_X, eval₂_C, sub_add_cancel]
  rw [eval₂_map]
  have hmap : GaussianInt.toComplex.comp (Int.castRingHom GI) = algebraMap ℤ ℂ :=
    Subsingleton.elim _ _
  rw [hmap]
  rfl

theorem polynomialPart_endpoint_expansion (n : ℕ) (hn : 1 ≤ n) (t : ℂ) :
    aeval t (polynomialPart n) =
      ∑ k ∈ Finset.range (7430 * n - 1),
        (endpointCoeff n k : ℂ) * (t - (-1 - 2 * Complex.I)) ^ k := by
  rw [← endpointPolynomial_eval, eval₂_eq_sum_range, endpointPolynomial_natDegree]
  have hdegree : 7430 * n - 2 + 1 = 7430 * n - 1 := by omega
  rw [hdegree, lowerEndpointGI_cast]
  rfl

theorem endpointMonomial_has_primitive (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => -Complex.I / (k + 1 : ℂ) *
      (verticalSegment s - (-1 - 2 * Complex.I)) ^ (k + 1))
      ((verticalSegment s - (-1 - 2 * Complex.I)) ^ k) s := by
  have hd := ((((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (-1)).sub_const
    (-1 - 2 * Complex.I)).pow (k + 1)
  have h := (hd.const_mul (-Complex.I / (k + 1 : ℂ))).comp_ofReal
  convert h using 1
  · rfl
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_mul]
    have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    field_simp
    ring_nf
    simp [Complex.I_sq, verticalSegment, mul_comm, add_comm, add_left_comm]

theorem endpointMonomial_integral (k : ℕ) :
    -(∫ s : ℝ in (-2)..2, (verticalSegment s - (-1 - 2 * Complex.I)) ^ k) =
      Complex.I * (4 * Complex.I) ^ (k + 1) / (k + 1 : ℂ) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => endpointMonomial_has_primitive k s)
    (((verticalSegment_continuous.sub continuous_const).pow k).intervalIntegrable _ _)]
  have hupper : verticalSegment 2 - (-1 - 2 * Complex.I) = 4 * Complex.I := by
    norm_num [verticalSegment]
    ring
  have hlower : verticalSegment (-2) - (-1 - 2 * Complex.I) = 0 := by
    norm_num [verticalSegment]
  rw [hupper, hlower, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]
  ring

theorem polynomialPart_endpoint_integral (n : ℕ) (hn : 1 ≤ n) :
    -(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (polynomialPart n)) =
      Complex.I * ∑ k ∈ Finset.range (7430 * n - 1),
        (endpointCoeff n k : ℂ) * (4 * Complex.I) ^ (k + 1) / (k + 1 : ℂ) := by
  simp_rw [polynomialPart_endpoint_expansion n hn]
  rw [intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, neg_mul_eq_mul_neg, endpointMonomial_integral]
    ring
  · intro k _
    exact (continuous_const.mul
      ((verticalSegment_continuous.sub continuous_const).pow k)).intervalIntegrable _ _

end PiIrrationality
