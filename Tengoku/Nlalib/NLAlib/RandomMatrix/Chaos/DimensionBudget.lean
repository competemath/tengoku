import Tengoku.Nlalib.NLAlib.RandomMatrix.Chaos.CoefficientRecursion
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.LogDimensionBudget

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The invariant coefficient-array dimension product

Moving a coefficient index into a matrix coordinate preserves the total number
of scalar coefficient entries. Its logarithm controls every linear step.
-/

noncomputable section
namespace NLAlib

/-- The product of the original matrix dimensions and every chaos-coordinate
dimension, equivalently the total number of scalar coefficient entries.-/
def chaosDimensionProduct (τ ι m n : Type*) [Fintype τ] [Fintype ι]
    [Fintype m] [Fintype n] : ℕ :=
  Fintype.card m * Fintype.card n * Fintype.card ι ^ Fintype.card τ

variable {τ ι m n : Type*} [Fintype τ] [Fintype ι] [Fintype m] [Fintype n]

/-- The horizontal coefficient branch preserves the entire array dimension
product.
@isnad1 id=eq.0h4v.s5.a41aac9f849d from=translated src=- shape=ad5f688e vocab=e2042d7a
-/
theorem chaosDimensionProduct_row :
    chaosDimensionProduct τ ι m (ι × n) = chaosDimensionProduct (τ ⊕ Unit) ι m n := by
  simp only [chaosDimensionProduct, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_punit, pow_add, pow_one]
  ring

/-- The vertical coefficient branch preserves the entire array dimension product.
@isnad1 id=eq.0h4v.s5.03f52d477c02 from=translated src=- shape=1330c62a vocab=e2042d7a
-/
theorem chaosDimensionProduct_column :
    chaosDimensionProduct τ ι (ι × m) n = chaosDimensionProduct (τ ⊕ Unit) ι m n := by
  simp only [chaosDimensionProduct, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_punit, pow_add, pow_one]
  ring

/-- The entry-vectorization branch preserves the entire array dimension product.
@isnad1 id=eq.0h4v.s5.15fd1f99e5f0 from=translated src=- shape=d731e99d vocab=e2042d7a
-/
theorem chaosDimensionProduct_entry :
    chaosDimensionProduct τ ι ι (m × n) = chaosDimensionProduct (τ ⊕ Unit) ι m n := by
  simp only [chaosDimensionProduct, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_punit, pow_add, pow_one]
  ring

/-- With at least one possible coordinate value, the current matrix dimension
product is no larger than the full coefficient-array product.
@isnad1 id=le.0h4v.s5.2c39b6e1585a from=translated src=- shape=8c25937f vocab=deae219f
-/
theorem card_mul_card_le_chaosDimensionProduct [Nonempty ι] :
    Fintype.card m * Fintype.card n ≤ chaosDimensionProduct τ ι m n := by
  exact Nat.le_mul_of_pos_right _ (pow_pos Fintype.card_pos _)

/-- Every current linear matrix-series logarithm is bounded by the same global
coefficient-array budget.
@isnad1 id=le.1h5v.s6.a87770c3a4b5 from=translated src=- shape=065c2c7b vocab=3804c537
-/
theorem log_matrix_dimension_le_chaos_budget [Nonempty ι] [Nonempty m] [Nonempty n]
    {D : ℕ} (hD : chaosDimensionProduct τ ι m n ≤ D) :
    Real.log (2 * ((Fintype.card m : ℝ) + Fintype.card n)) ≤ Real.log (4 * D) := by
  apply Real.log_two_mul_add_le_log_four_mul
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card m ≠ 0))
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card n ≠ 0))
  · exact_mod_cast (card_mul_card_le_chaosDimensionProduct (τ := τ)).trans hD

end NLAlib
