import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.LaurentIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open MeasureTheory Polynomial
namespace XZMathieuSU2Counterexamples

def basic : Laurent := (1 - LaurentPolynomial.T (-1)) *
  (LaurentPolynomial.C (1 - X) + LaurentPolynomial.C X * LaurentPolynomial.T 1)

/--
@isnad1 id=eq.0h1v.s5.b5a42ed60fa1 from=translated src=- shape=357f4f17 vocab=91b62627
-/
theorem basic_specialize (x : ℂ) : specialize x basic = xzFamily x := by
  simp [basic, xzFamily, xzA, add_comm]

/--
@isnad1 id=eq.1h1v.s5.dd38b3217207 from=translated src=- shape=2467d181 vocab=51668092
-/
theorem basic_pure (n : ℕ) (hn : 1 ≤ n) : integral (basic ^ n) = 0 := by
  unfold integral
  simp_rw [← specialize_coeff, map_pow, basic_specialize]
  exact xzFamily_integral_pure n hn

/--
@isnad1 id=eq.1h1v.s7.193a50ca2c6e from=translated src=- shape=6e111173 vocab=bc656e16
-/
theorem basic_marked (n : ℕ) (hn : 1 ≤ n) :
    integral (LaurentPolynomial.T (-1) * basic ^ n) = (-1 : ℂ) ^ (n-1) / (n+1) := by
  unfold integral
  have he : (LaurentPolynomial.T (-1) * basic ^ n).coeff 0 = (basic ^ n).coeff 1 := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
    rfl
  rw [he]
  simp_rw [← specialize_coeff, map_pow, basic_specialize]
  exact xzFamily_integral_marked n hn

/--
@isnad1 id=ne.1h1v.s6.c99e85c933d7 from=translated src=- shape=962c035f vocab=c50a9385
-/
theorem basic_marked_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    integral (LaurentPolynomial.T (-1) * basic ^ n) ≠ 0 := by
  rw [basic_marked n hn]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.succ_ne_zero n)

/--
@isnad1 id=eq.0h0v.s9.d3f05956dfb6 from=translated src=- shape=f940d658 vocab=1a633f40
-/
theorem basic_expansion : basic =
    LaurentPolynomial.C (X - 1) * LaurentPolynomial.T (-1) +
    LaurentPolynomial.C (1 - 2 * X) +
    LaurentPolynomial.C (X) * LaurentPolynomial.T 1 := by
  have ht : (LaurentPolynomial.T (-1) : Laurent) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [basic, map_sub, map_one, map_mul, map_ofNat]
  linear_combination -LaurentPolynomial.C (X) * ht

/--
@isnad1 id=eq.0h1v.s8.ae7f49d3d767 from=translated src=- shape=3c75048b vocab=289e2de0
-/
theorem basic_coeff (k : ℤ) : basic.coeff k =
    (if k = -1 then X - 1 else 0) +
    (if k = 0 then 1 - 2 * X else 0) +
    (if k = 1 then X else 0) := by
  rw [basic_expansion]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    LaurentPolynomial.C_apply, Finsupp.single_apply]
  simp [eq_comm]

/--
@isnad1 id=eq.0h0v.s6.488334b76cfc from=translated src=- shape=99e78a8c vocab=371fd4b7
-/
theorem basic_spectrum : basic.coeff.support = {-1, 0, 1} := by
  classical
  have hneg : (X - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num at hh
  have hzero : (1 - 2 * X : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num at hh
  ext k
  simp only [Finsupp.mem_support_iff, basic_coeff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hkneg : k = -1
  · subst k; simpa using hneg
  by_cases hkzero : k = 0
  · subst k; simpa using hzero
  by_cases hkpos : k = 1
  · subst k; simp
  · simp [hkneg, hkzero, hkpos]

/--
@isnad1 id=mem.0h0v.s6.fd5fc75fa80f from=translated src=- shape=b973bdc8 vocab=16db37f2
-/
theorem basic_zero_mem_convexHull : (0 : ℝ) ∈
    convexHull ℝ ((fun k : ℤ => (k : ℝ)) '' (basic.coeff.support : Set ℤ)) := by
  apply subset_convexHull ℝ
  exact ⟨0, by simp [basic_spectrum], by simp⟩

/--
@isnad1 id=not.0h0v.s1.131881994701 from=translated src=- shape=49959d42 vocab=782cdaf8
-/
theorem not_XZConjecture : ¬ XZConjecture := by
  intro h
  exact h basic basic_pure basic_zero_mem_convexHull

/--
@isnad1 id=not.0h0v.s7.10282bdf15d1 from=translated src=- shape=5a6bd475 vocab=08f14162
-/
theorem kernel_not_mathieu : ¬ IsMathieuSubspace (LinearMap.ker integralLinear) :=
  not_isMathieuSubspace_of_witness _ basic (LaurentPolynomial.T (-1))
    basic_pure basic_marked_ne_zero

/-- Theorem 2.1, including its exact spectrum and both stated consequences.
@isnad1 id=and.0h0v.s8.1b6de3e6ecf5 from=translated src=- shape=e8633955 vocab=81164ccf
-/
theorem basic_xz :
    (∀ n : ℕ, 1 ≤ n → integral (basic ^ n) = 0) ∧
    (∀ n : ℕ, 1 ≤ n → integral (LaurentPolynomial.T (-1) * basic ^ n) =
      (-1 : ℂ) ^ (n-1) / (n+1)) ∧
    basic.coeff.support = {-1,0,1} ∧ ¬ XZConjecture ∧
    ¬ IsMathieuSubspace (LinearMap.ker integralLinear) :=
  ⟨basic_pure, basic_marked, basic_spectrum, not_XZConjecture, kernel_not_mathieu⟩

end XZMathieuSU2Counterexamples
