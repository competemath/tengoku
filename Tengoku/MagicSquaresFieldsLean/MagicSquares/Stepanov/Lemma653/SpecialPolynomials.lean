import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma645.Sets
import Tengoku.Seed.Algebra.Polynomial.Monic
import Tengoku.Seed.Algebra.Polynomial.Degree.Operations
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# The two choices of B in LN97 Theorem 6.53

* `B1(X)=X-1`;
* `B2(X)=X^(m-1)+...+X+1`.
-/

/-- First special polynomial, `X-1`.-/
noncomputable def theorem653B1 : Polynomial F := X - 1

@[simp] theorem theorem653B1_monic :
    (theorem653B1 : Polynomial F).Monic := by
  simpa [theorem653B1] using
    (Polynomial.monic_X_sub_C (1 : F))

@[simp] theorem theorem653B1_natDegree :
    (theorem653B1 : Polynomial F).natDegree = 1 := by
  simpa [theorem653B1] using
    (Polynomial.natDegree_X_sub_C (1 : F))

/-- Second special polynomial, the geometric factor.-/
noncomputable def theorem653B2 (m : ℕ) : Polynomial F :=
  geometricPolynomial (F := F) m

/-- For `m>1`, the geometric polynomial has degree `m-1`.-/
theorem theorem653B2_natDegree
    (m : ℕ) (hm : 1 < m) :
    (theorem653B2 (F := F) m).natDegree = m - 1 := by
  unfold theorem653B2 geometricPolynomial
  have hm0 : m ≠ 0 := by omega
  have hpred : m - 1 < m := Nat.pred_lt hm0
  have hlead :
      (∑ i ∈ Finset.range m, (X : Polynomial F) ^ i).coeff (m - 1) = 1 := by
    simp [Polynomial.coeff_X_pow, hpred]
  apply le_antisymm
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    rw [Polynomial.natDegree_pow]
    simp
    omega
  · exact Polynomial.le_natDegree_of_ne_zero (by simpa using hlead)

end LN97
end MagicSquares
