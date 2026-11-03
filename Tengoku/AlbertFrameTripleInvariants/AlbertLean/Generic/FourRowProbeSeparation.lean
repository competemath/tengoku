import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms twoByTwo_separates` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairDet_zero_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairDet_zero_two` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairDet_one_two` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairProbes_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rowSymMeasurements_injective` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Division-free `3 x 3` probe separation

This ordinary matrix lemma contains no Albert model or frame attachment.
-/

namespace AlbertLean.Generic.FourRowProbeSeparation

abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

variable {K : Type*} [Field K]

/-- The oriented three-cycle difference.-/
def cycleDifference (F : Mat3 K) : K :=
  F 0 1 * F 1 2 * F 2 0 - F 1 0 * F 2 1 * F 0 2

/-- The symmetric contribution of the unordered pair `{i,k}` to row probes.-/
def pairProbe (F A : Mat3 K) (i k : Fin 3) : K :=
  F i k * A k i + F k i * A i k

/-- Division-free symmetric-row measurements. The diagonal summand is
`2 * F i i * A i i`.-/
def rowSymMeasurements (F A : Mat3 K) (i : Fin 3) : K :=
  ∑ k : Fin 3, (F i k * A k i + F k i * A i k)

def offRowMeasurement (F A : Mat3 K) (i : Fin 3) : K :=
  rowSymMeasurements F A i - 2 * F i i * A i i

/-- A nonsingular scalar `2 x 2` coefficient matrix separates both unknowns.
@isnad1 id=and.3h9v.s8.a8b1ca23e1a4 from=translated src=- shape=f39693e5 vocab=5f818f28
-/
theorem twoByTwo_separates {a b c d x y x' y' : K}
    (hdet : a * d - b * c ≠ 0)
    (h₁ : a * x + b * y = a * x' + b * y')
    (h₂ : c * x + d * y = c * x' + d * y') :
    x = x' ∧ y = y' := by
  have hxprod : (a * d - b * c) * (x - x') = 0 := by
    linear_combination d * h₁ - b * h₂
  have hyprod : (a * d - b * c) * (y - y') = 0 := by
    linear_combination a * h₂ - c * h₁
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hxprod).resolve_left hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hyprod).resolve_left hdet)⟩

/--
@isnad1 id=eq.0h3v.s7.b3523620bc21 from=translated src=- shape=3f047e42 vocab=5cbd5e78
-/
theorem offRow_combo_zero_one (F A : Mat3 K) :
    offRowMeasurement F A 0 + offRowMeasurement F A 1 -
      offRowMeasurement F A 2 = 2 * pairProbe F A 0 1 := by
  simp [offRowMeasurement, rowSymMeasurements, pairProbe, Fin.sum_univ_succ]
  ring

/--
@isnad1 id=eq.0h3v.s7.a04541726426 from=translated src=- shape=3f047e42 vocab=5cbd5e78
-/
theorem offRow_combo_zero_two (F A : Mat3 K) :
    offRowMeasurement F A 0 + offRowMeasurement F A 2 -
      offRowMeasurement F A 1 = 2 * pairProbe F A 0 2 := by
  simp [offRowMeasurement, rowSymMeasurements, pairProbe, Fin.sum_univ_succ]
  ring

/--
@isnad1 id=eq.0h3v.s7.91adf7d214fe from=translated src=- shape=3f047e42 vocab=5cbd5e78
-/
theorem offRow_combo_one_two (F A : Mat3 K) :
    offRowMeasurement F A 1 + offRowMeasurement F A 2 -
      offRowMeasurement F A 0 = 2 * pairProbe F A 1 2 := by
  simp [offRowMeasurement, rowSymMeasurements, pairProbe, Fin.sum_univ_succ]
  ring

/--
@isnad1 id=eq.0h2v.s8.fd6b02e193a2 from=translated src=- shape=479e7898 vocab=52c1d5df
-/
theorem pairDet_zero_one (F : Mat3 K) :
    F 0 1 * (F * F) 1 0 - F 1 0 * (F * F) 0 1 = cycleDifference F := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, cycleDifference]
  ring

/--
@isnad1 id=eq.0h2v.s8.83343ebb816f from=translated src=- shape=52872e37 vocab=8e18e8d2
-/
theorem pairDet_zero_two (F : Mat3 K) :
    F 0 2 * (F * F) 2 0 - F 2 0 * (F * F) 0 2 = -cycleDifference F := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, cycleDifference]
  ring

/--
@isnad1 id=eq.0h2v.s8.fd114e2a5b2f from=translated src=- shape=479e7898 vocab=52c1d5df
-/
theorem pairDet_one_two (F : Mat3 K) :
    F 1 2 * (F * F) 2 1 - F 2 1 * (F * F) 1 2 = cycleDifference F := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, cycleDifference]
  ring

/--
@isnad1 id=and.3h6v.s8.f15989bc5d73 from=translated src=- shape=b91ddacf vocab=963ad876
-/
theorem pair_separates (F A B : Mat3 K) (i k : Fin 3)
    (hdet : F i k * (F * F) k i - F k i * (F * F) i k ≠ 0)
    (h₁ : pairProbe F A i k = pairProbe F B i k)
    (h₂ : pairProbe (F * F) A i k = pairProbe (F * F) B i k) :
    A k i = B k i ∧ A i k = B i k := by
  exact twoByTwo_separates hdet h₁ h₂

/-- Equal diagonal and pair probes for `F` and `F^2` determine the matrix.
@isnad1 id=eq.4h4v.s9.6894b8012a19 from=translated src=- shape=04d896b1 vocab=d70ab3e0
-/
theorem pairProbes_injective (F A B : Mat3 K)
    (hDelta : cycleDifference F ≠ 0)
    (hDiag : ∀ i, A i i = B i i)
    (hFirst : pairProbe F A 0 1 = pairProbe F B 0 1 ∧
      pairProbe F A 0 2 = pairProbe F B 0 2 ∧ pairProbe F A 1 2 = pairProbe F B 1 2)
    (hSecond : pairProbe (F * F) A 0 1 = pairProbe (F * F) B 0 1 ∧
      pairProbe (F * F) A 0 2 = pairProbe (F * F) B 0 2 ∧
      pairProbe (F * F) A 1 2 = pairProbe (F * F) B 1 2) :
    A = B := by
  have h01 := pair_separates F A B 0 1
    (by rw [pairDet_zero_one]; exact hDelta)
    hFirst.1 hSecond.1
  have h02 := pair_separates F A B 0 2
    (by rw [pairDet_zero_two]; exact neg_ne_zero.mpr hDelta)
    hFirst.2.1 hSecond.2.1
  have h12 := pair_separates F A B 1 2
    (by rw [pairDet_one_two]; exact hDelta)
    hFirst.2.2 hSecond.2.2
  ext i k
  fin_cases i <;> fin_cases k
  all_goals simp_all

private theorem offRow_eq_of_row_diag (F A B : Mat3 K)
    (hDiag : ∀ i, A i i = B i i)
    (hRow : rowSymMeasurements F A = rowSymMeasurements F B) (i : Fin 3) :
    offRowMeasurement F A i = offRowMeasurement F B i := by
  rw [offRowMeasurement, offRowMeasurement, congrFun hRow i, hDiag i]

private theorem cancel_two {x y : K} (hTwo : (2 : K) ≠ 0)
    (h : 2 * x = 2 * y) : x = y := by
  exact mul_left_cancel₀ hTwo h

/-- Three symmetric rows for `F` and `F^2`, together with the diagonal,
determine every entry when the cycle difference is nonzero.
@isnad1 id=eq.5h4v.s8.d4833ad9a622 from=translated src=- shape=08f1b1c3 vocab=2bc95356
-/
theorem rowSymMeasurements_injective (F A B : Mat3 K)
    (hTwo : (2 : K) ≠ 0)
    (hDelta : cycleDifference F ≠ 0)
    (hDiag : ∀ i, A i i = B i i)
    (hFirst : rowSymMeasurements F A = rowSymMeasurements F B)
    (hSecond : rowSymMeasurements (F * F) A = rowSymMeasurements (F * F) B) :
    A = B := by
  have hOffFirst : ∀ i, offRowMeasurement F A i = offRowMeasurement F B i :=
    offRow_eq_of_row_diag F A B hDiag hFirst
  have hOffSecond : ∀ i,
      offRowMeasurement (F * F) A i = offRowMeasurement (F * F) B i :=
    offRow_eq_of_row_diag (F * F) A B hDiag hSecond
  have hp01 : pairProbe F A 0 1 = pairProbe F B 0 1 := by
    apply cancel_two hTwo
    rw [← offRow_combo_zero_one F A, ← offRow_combo_zero_one F B]
    simp only [hOffFirst]
  have hp02 : pairProbe F A 0 2 = pairProbe F B 0 2 := by
    apply cancel_two hTwo
    rw [← offRow_combo_zero_two F A, ← offRow_combo_zero_two F B]
    simp only [hOffFirst]
  have hp12 : pairProbe F A 1 2 = pairProbe F B 1 2 := by
    apply cancel_two hTwo
    rw [← offRow_combo_one_two F A, ← offRow_combo_one_two F B]
    simp only [hOffFirst]
  have hp201 : pairProbe (F * F) A 0 1 = pairProbe (F * F) B 0 1 := by
    apply cancel_two hTwo
    rw [← offRow_combo_zero_one (F * F) A,
      ← offRow_combo_zero_one (F * F) B]
    simp only [hOffSecond]
  have hp202 : pairProbe (F * F) A 0 2 = pairProbe (F * F) B 0 2 := by
    apply cancel_two hTwo
    rw [← offRow_combo_zero_two (F * F) A,
      ← offRow_combo_zero_two (F * F) B]
    simp only [hOffSecond]
  have hp212 : pairProbe (F * F) A 1 2 = pairProbe (F * F) B 1 2 := by
    apply cancel_two hTwo
    rw [← offRow_combo_one_two (F * F) A,
      ← offRow_combo_one_two (F * F) B]
    simp only [hOffSecond]
  exact pairProbes_injective F A B hDelta hDiag
    ⟨hp01, hp02, hp12⟩ ⟨hp201, hp202, hp212⟩

end AlbertLean.Generic.FourRowProbeSeparation
