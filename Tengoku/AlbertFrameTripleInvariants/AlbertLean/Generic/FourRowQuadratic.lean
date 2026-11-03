import Tengoku.Seed.Algebra.Polynomial.Eval.Degree
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms coeff_two_satisfies_quadratic_of_cubic_factorization` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The scalar quadratic forced by two normalized cubic factors

This file isolates the commutative polynomial calculation in the first-Tits
matrix reduction.  No matrix model or Albert-algebra assertion occurs here.
-/

noncomputable section

namespace AlbertLean.Generic.FourRowQuadratic

open Polynomial

variable {R : Type*} [CommRing R]

/-- The one-parameter monic cubic with value `-c` at zero and value `d` at
minus one.-/
def cubicNormalForm (c d s : R) : R[X] :=
  X ^ 3 + C s * X ^ 2 + C (s - (1 + c + d)) * X - C c

/--
@isnad1 id=eq.0h4v.s5.88062295a255 from=translated src=- shape=3520aa0a vocab=4d15d4c4
-/
@[simp]
theorem cubicNormalForm_eval_zero (c d s : R) :
    (cubicNormalForm c d s).eval 0 = -c := by
  simp [cubicNormalForm]

/--
@isnad1 id=eq.0h4v.s5.53cd85d03353 from=translated src=- shape=e6bbd816 vocab=4d15d4c4
-/
@[simp]
theorem cubicNormalForm_eval_neg_one (c d s : R) :
    (cubicNormalForm c d s).eval (-1) = d := by
  simp [cubicNormalForm]
  ring

/-- The endpoint values determine the linear coefficient of a cubic once its
quadratic parameter and leading coefficient are fixed.
@isnad1 id=eq.4h4v.s7.00470ad5fefb from=translated src=- shape=b1bf8ac9 vocab=8537188f
-/
theorem coeff_one_eq_of_cubic_endpoints
    (q : R[X]) (c d : R)
    (hqDegree : q.natDegree <= 3)
    (hqLead : q.coeff 3 = 1)
    (hqZero : q.eval 0 = -c)
    (hqNegOne : q.eval (-1) = d) :
    q.coeff 1 = q.coeff 2 - (1 + c + d) := by
  have hqConst : q.coeff 0 = -c := by
    exact q.coeff_zero_eq_eval_zero.trans hqZero
  have hqExpansion :=
    q.eval_eq_sum_range' (n := 4) (lt_of_le_of_lt hqDegree (by omega)) (-1)
  rw [hqNegOne] at hqExpansion
  simp [Finset.sum_range_succ, hqConst, hqLead] at hqExpansion
  linear_combination hqExpansion

/-- A degree-at-most-three polynomial with leading coefficient one and the two
specified endpoint values is exactly the displayed one-parameter cubic.-/
theorem eq_cubicNormalForm_of_endpoints
    (q : R[X]) (c d : R)
    (hqDegree : q.natDegree <= 3)
    (hqLead : q.coeff 3 = 1)
    (hqZero : q.eval 0 = -c)
    (hqNegOne : q.eval (-1) = d) :
    q = cubicNormalForm c d (q.coeff 2) := by
  have hqConst : q.coeff 0 = -c := by
    exact q.coeff_zero_eq_eval_zero.trans hqZero
  have hqLinear : q.coeff 1 = q.coeff 2 - (1 + c + d) :=
    coeff_one_eq_of_cubic_endpoints q c d hqDegree hqLead hqZero hqNegOne
  ext n
  by_cases h0 : n = 0
  · subst n
    simp only [cubicNormalForm, coeff_sub, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    simp [hqConst]
  by_cases h1 : n = 1
  · subst n
    simp only [cubicNormalForm, coeff_sub, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    simp [hqLinear]
  by_cases h2 : n = 2
  · subst n
    simp only [cubicNormalForm, coeff_sub, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    simp
  by_cases h3 : n = 3
  · subst n
    simp only [cubicNormalForm, coeff_sub, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    simp [hqLead]
  have hn : 3 < n := by omega
  have hqn : q.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (hqDegree.trans_lt hn)
  rw [hqn]
  simp only [cubicNormalForm, coeff_sub, coeff_add, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp [h0, h1, h2, h3]

/-- Only the two `(2,3)` and `(3,2)` summands can contribute to coefficient
five in a product of degree-at-most-three polynomials.
@isnad1 id=eq.2h3v.s7.a71b20f9b0c2 from=translated src=- shape=2cd5956e vocab=705205c1
-/
theorem coeff_five_mul_of_cubic_bounds
    (q r : R[X])
    (hqDegree : q.natDegree <= 3)
    (hrDegree : r.natDegree <= 3) :
    (q * r).coeff 5 = q.coeff 2 * r.coeff 3 + q.coeff 3 * r.coeff 2 := by
  have hq4 : q.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hqDegree.trans_lt (by omega))
  have hq5 : q.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hqDegree.trans_lt (by omega))
  have hr4 : r.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hrDegree.trans_lt (by omega))
  have hr5 : r.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hrDegree.trans_lt (by omega))
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, hq4, hq5, hr4, hr5]

/-- Only the three central summands can contribute to coefficient four in a
product of degree-at-most-three polynomials.
@isnad1 id=eq.2h3v.s8.356efddb3bd6 from=translated src=- shape=83701c39 vocab=705205c1
-/
theorem coeff_four_mul_of_cubic_bounds
    (q r : R[X])
    (hqDegree : q.natDegree <= 3)
    (hrDegree : r.natDegree <= 3) :
    (q * r).coeff 4 =
      q.coeff 1 * r.coeff 3 + q.coeff 2 * r.coeff 2 + q.coeff 3 * r.coeff 1 := by
  have hq4 : q.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hqDegree.trans_lt (by omega))
  have hr4 : r.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hrDegree.trans_lt (by omega))
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, hq4, hr4]

/-- Two normalized monic cubic factors force the quadratic relation used in
the first-Tits scalar reduction.  All hypotheses needed by the polynomial
calculation are explicit; the theorem does not assert that a matrix problem
supplies such a factorization.
@isnad1 id=eq.9h6v.s9.0307e9ec0d5a from=translated src=- shape=f1222896 vocab=966cd021
-/
theorem coeff_two_satisfies_quadratic_of_cubic_factorization
    (q r p : R[X]) (c d : R)
    (hqDegree : q.natDegree <= 3)
    (hrDegree : r.natDegree <= 3)
    (hqLead : q.coeff 3 = 1)
    (hrLead : r.coeff 3 = 1)
    (hqZero : q.eval 0 = -c)
    (hrZero : r.eval 0 = -c)
    (hqNegOne : q.eval (-1) = d)
    (hrNegOne : r.eval (-1) = d)
    (hFactor : p = q * r) :
    q.coeff 2 ^ 2 - p.coeff 5 * q.coeff 2 +
        (p.coeff 4 + 2 * (1 + c + d) - p.coeff 5) = 0 := by
  have hqNormal :=
    eq_cubicNormalForm_of_endpoints q c d hqDegree hqLead hqZero hqNegOne
  have hrNormal :=
    eq_cubicNormalForm_of_endpoints r c d hrDegree hrLead hrZero hrNegOne
  have hqLinear : q.coeff 1 = q.coeff 2 - (1 + c + d) := by
    simpa [cubicNormalForm] using congrArg (fun f : R[X] => f.coeff 1) hqNormal
  have hrLinear : r.coeff 1 = r.coeff 2 - (1 + c + d) := by
    simpa [cubicNormalForm] using congrArg (fun f : R[X] => f.coeff 1) hrNormal
  have hpFive : p.coeff 5 = q.coeff 2 + r.coeff 2 := by
    rw [hFactor,
      coeff_five_mul_of_cubic_bounds q r hqDegree hrDegree,
      hqLead, hrLead]
    ring
  have hpFour :
      p.coeff 4 = q.coeff 1 + q.coeff 2 * r.coeff 2 + r.coeff 1 := by
    rw [hFactor,
      coeff_four_mul_of_cubic_bounds q r hqDegree hrDegree,
      hqLead, hrLead]
    ring
  rw [hpFive, hpFour, hqLinear, hrLinear]
  ring

end AlbertLean.Generic.FourRowQuadratic
