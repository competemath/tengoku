import Tengoku.WasowAsymptoticsLean.WasowReductionDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms rowPolynomial_coeff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rowPolynomial_eq_zero_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rowPolynomial_ne_zero_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms natDegree_rowPolynomial_lt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rowPolynomial_eq_sum_C_mul_X_pow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms neg_rowPolynomial_nonzero_degree` (it only prints; the queue checks the axioms of every declaration). -/

/-! The coefficients surviving the elimination of a nilpotent shift block.
The polynomial records its actual last-row entries, so its nonvanishing and
degree bound are conclusions, not extra assumptions on the reduced pencil. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
namespace WasowPencilCoefficients

def rowPolynomial {h : ℕ} (v : Fin (h+1) → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (v i)

/--
@isnad1 id=eq.0h3v.s5.f5a0913cee42 from=translated src=- shape=5fb1c943 vocab=7d78b3f0
-/
theorem rowPolynomial_coeff {h : ℕ} (v : Fin (h+1) → ℂ) (i : Fin (h+1)) :
    (rowPolynomial v).coeff i.val = v i := by
  classical
  simp only [rowPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [ite_eq_right (fun he => hji (Fin.ext he))]
  · simp

/--
@isnad1 id=iff.0h2v.s6.966f594e6617 from=translated src=- shape=68ba2187 vocab=0cb4c8de
-/
theorem rowPolynomial_eq_zero_iff {h : ℕ} (v : Fin (h+1) → ℂ) :
    rowPolynomial v = 0 ↔ ∀ i, v i = 0 := by
  constructor
  · intro hv i
    have he := congrArg (fun p : Polynomial ℂ => p.coeff i.val) hv
    simpa only [rowPolynomial_coeff, Polynomial.coeff_zero] using he
  · intro hv
    simp [rowPolynomial, hv]

/--
@isnad1 id=iff.0h2v.s6.61aeb8e74f44 from=translated src=- shape=dd51519a vocab=0cb4c8de
-/
theorem rowPolynomial_ne_zero_iff {h : ℕ} (v : Fin (h+1) → ℂ) :
    rowPolynomial v ≠ 0 ↔ ∃ i, v i ≠ 0 := by
  simp only [ne_eq, rowPolynomial_eq_zero_iff, not_forall]

/--
@isnad1 id=lt.0h2v.s5.a61e89524240 from=translated src=- shape=0b421e17 vocab=c2273610
-/
theorem natDegree_rowPolynomial_lt {h : ℕ} (v : Fin (h+1) → ℂ) :
    (rowPolynomial v).natDegree < h+1 := by
  apply Nat.lt_succ_of_le
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le (v i)).trans (by omega)

/--
@isnad1 id=eq.0h2v.s7.7b8620d0a327 from=translated src=- shape=ce4aed5b vocab=edfbf6e5
-/
theorem rowPolynomial_eq_sum_C_mul_X_pow {h : ℕ} (v : Fin (h+1) → ℂ) :
    rowPolynomial v = ∑ i, Polynomial.C (v i) * X^i.val := by
  simp only [rowPolynomial, Polynomial.C_mul_X_pow_eq_monomial]

/-- Thus every nonzero rectangular last row gives a nonzero reduced entry
of degree strictly below its column block size.
@isnad1 id=and.1h2v.s6.0279685cc791 from=translated src=- shape=755832b0 vocab=1d8499e4
-/
theorem neg_rowPolynomial_nonzero_degree {h : ℕ} (v : Fin (h+1) → ℂ)
    (hv : ∃ i, v i ≠ 0) :
    -rowPolynomial v ≠ 0 ∧ (-rowPolynomial v).natDegree < h+1 := by
  exact ⟨neg_ne_zero.mpr ((rowPolynomial_ne_zero_iff v).mpr hv),
    by simpa only [Polynomial.natDegree_neg] using natDegree_rowPolynomial_lt v⟩

end WasowPencilCoefficients
