import Tengoku.Piirrationalitymeasure.Formalization.PolynomialPart
import Tengoku.Piirrationalitymeasure.Formalization.GaussianIntegrality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact rational evaluation of the polynomial contribution to `J_n`.
The endpoint powers are Gaussian integers, so their imaginary parts give
explicit rational coefficients after termwise integration.
-/

namespace PiIrrationality

open Polynomial

def verticalSegment (s : ℝ) : ℂ := -1 + (s : ℂ) * Complex.I

/--
@isnad1 id=continuo.0h0v.s4.58e249e7dd9e from=translated src=- shape=54c8eceb vocab=a209731b
-/
theorem verticalSegment_continuous : Continuous verticalSegment := by
  unfold verticalSegment
  fun_prop

def upperEndpointGI : GI := ⟨-1, 2⟩

/--
@isnad1 id=eq.0h0v.s6.fe6dc1994446 from=translated src=- shape=6542c990 vocab=6b3cea6d
-/
theorem upperEndpointGI_cast : (upperEndpointGI : ℂ) = -1 + 2 * Complex.I := by
  simp [upperEndpointGI, GaussianInt.toComplex_def']

/--
@isnad1 id=hasderiv.0h2v.s7.97e603337096 from=translated src=- shape=2fb28b79 vocab=0540fc8e
-/
theorem verticalMonomial_has_primitive (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => -Complex.I / (k + 1 : ℂ) * verticalSegment s ^ (k + 1))
      (verticalSegment s ^ k) s := by
  have hd := (((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (-1)).pow (k + 1)
  have h := (hd.const_mul (-Complex.I / (k + 1 : ℂ))).comp_ofReal
  convert h using 1
  · rfl
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_mul]
    have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    field_simp
    ring_nf
    simp [Complex.I_sq, verticalSegment, mul_comm]

/--
@isnad1 id=eq.0h1v.s7.dd61135277bd from=translated src=- shape=6179904c vocab=942088b7
-/
theorem verticalMonomial_integral (k : ℕ) :
    -(∫ s : ℝ in (-2)..2, verticalSegment s ^ k) =
      Complex.I / (k + 1 : ℂ) *
        ((-1 + 2 * Complex.I) ^ (k + 1) - (-1 - 2 * Complex.I) ^ (k + 1)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => verticalMonomial_has_primitive k s)
    ((verticalSegment_continuous.pow k).intervalIntegrable _ _)]
  simp only [verticalSegment]
  push_cast
  ring

/--
@isnad1 id=eq.0h1v.s7.3aa3d5c5f28b from=translated src=- shape=6d82db0f vocab=288b2a57
-/
theorem upperEndpoint_power_difference (k : ℕ) :
    (-1 + 2 * Complex.I) ^ k - (-1 - 2 * Complex.I) ^ k =
      2 * (((upperEndpointGI ^ k).im : ℤ) : ℂ) * Complex.I := by
  have hc : (-1 - 2 * Complex.I) ^ k =
      star ((upperEndpointGI ^ k : GI) : ℂ) := by
    rw [map_pow, upperEndpointGI_cast]
    simp [sub_eq_add_neg]
  rw [hc, ← upperEndpointGI_cast, ← map_pow]
  rw [GaussianInt.toComplex_def]
  simp only [map_add, map_mul, Complex.star_def, map_intCast,
    Complex.conj_I]
  ring

noncomputable def verticalMonomialIntegralRat (k : ℕ) : ℚ :=
  -2 * ((upperEndpointGI ^ (k + 1)).im : ℚ) / (k + 1)

/--
@isnad1 id=eq.0h1v.s6.f1f759bc8e38 from=translated src=- shape=19aae9df vocab=51cfad55
-/
theorem verticalMonomial_integral_rat (k : ℕ) :
    -(∫ s : ℝ in (-2)..2, verticalSegment s ^ k) =
      (verticalMonomialIntegralRat k : ℂ) := by
  rw [verticalMonomial_integral, upperEndpoint_power_difference]
  unfold verticalMonomialIntegralRat
  push_cast
  ring_nf
  simp [Complex.I_sq]

noncomputable def verticalPolynomialIntegralRat (P : Polynomial ℤ) : ℚ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k : ℚ) * verticalMonomialIntegralRat k

/--
@isnad1 id=eq.0h1v.s7.565763faa322 from=translated src=- shape=6e07dd08 vocab=7fe7b982
-/
theorem verticalPolynomial_integral_rat (P : Polynomial ℤ) :
    -(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) P) =
      (verticalPolynomialIntegralRat P : ℂ) := by
  simp only [aeval_def, eval₂_eq_sum_range]
  rw [intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_neg_distrib]
    unfold verticalPolynomialIntegralRat
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, neg_mul_eq_mul_neg,
      verticalMonomial_integral_rat]
    rfl
  · intro k _
    exact (continuous_const.mul (verticalSegment_continuous.pow k)).intervalIntegrable _ _

end PiIrrationality
