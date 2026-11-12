import Tengoku.Seed.LinearAlgebra.Matrix.Rank
import Tengoku.Seed.LinearAlgebra.Matrix.Nonsingular
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Lemmas
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonzero minors of a full-row-rank matrix

A basis extracted from the columns selects a square minor. Ordered embeddings
index all column minors and their
sum of squares is positive at full row rank over the reals.
-/

noncomputable section

namespace AbelFormalization

variable {K ι : Type*} [Field K] [Fintype ι] {n : ℕ}

/-- Full row rank gives an injectively selected square minor with nonzero
determinant.
@isnad1 id=ex.1h4v.s6.06bc2f0b5d71 from=translated src=- shape=30cd28f0 vocab=ae062b5a
-/
theorem exists_column_minor_of_rank_eq
    (A : Matrix (Fin n) ι K) (hA : A.rank = n) :
    ∃ c : Fin n ↪ ι, (A.submatrix id c).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols]
    exact hA
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let c : Fin n ↪ ι := ⟨a ∘ e.symm, ha.comp e.symm.injective⟩
  refine ⟨c, ?_⟩
  have hminor : LinearIndependent K (A.submatrix id c).col := by
    change LinearIndependent K ((A.col ∘ a) ∘ e.symm)
    exact hli.comp e.symm e.symm.injective
  exact Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_col hminor)

/-- Full row rank of a product gives a nonzero full-row-size column minor
of the first factor. This is the matrix implication used by the chain rule.
@isnad1 id=ex.1h6v.s7.32d43b790982 from=translated src=- shape=38bdc85a vocab=d14f210e
-/
theorem exists_column_minor_of_rank_mul_eq
    {κ : Type*} [Fintype κ]
    (A : Matrix (Fin n) ι K) (B : Matrix ι κ K)
    (hAB : (A * B).rank = n) :
    ∃ c : Fin n ↪ ι, (A.submatrix id c).det ≠ 0 := by
  have hA : A.rank = n := le_antisymm
    (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height A)
    (hAB.symm.trans_le (Matrix.rank_mul_le_left A B))
  exact exists_column_minor_of_rank_eq A hA

section SumSquares

variable {S : Type*} [CommRing S]

/-- The finite sum of squares of all ordered column minors. Each column
selection is injective; permutations may repeat the same squared minor.-/
def sumSquaresColumnMinors (A : Matrix (Fin n) ι S) : S := by
  classical
  exact ∑ c : Fin n ↪ ι, (A.submatrix id c).det ^ 2

end SumSquares

/--
@isnad1 id=le.0h3v.s4.ba9e2abb9a2d from=translated src=- shape=09699097 vocab=798c35cd
-/
theorem sumSquaresColumnMinors_nonneg (A : Matrix (Fin n) ι ℝ) :
    0 ≤ sumSquaresColumnMinors A := by
  classical
  unfold sumSquaresColumnMinors
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- At full row rank, the squared-minor sum is strictly positive.
@isnad1 id=lt.1h3v.s5.750b73767060 from=translated src=- shape=1abfe4ba vocab=76aa3335
-/
theorem sumSquaresColumnMinors_pos_of_rank_eq
    (A : Matrix (Fin n) ι ℝ) (hA : A.rank = n) :
    0 < sumSquaresColumnMinors A := by
  classical
  obtain ⟨c, hc⟩ := exists_column_minor_of_rank_eq A hA
  unfold sumSquaresColumnMinors
  exact (sq_pos_of_ne_zero hc).trans_le
    (Finset.single_le_sum (fun (b : Fin n ↪ ι) _ => sq_nonneg ((A.submatrix id b).det))
      (Finset.mem_univ c))

/-- The squared formal-minor sum is positive when a chain-rule product has
full row rank.
@isnad1 id=lt.1h5v.s6.eb99f53bc302 from=translated src=- shape=9d7715f2 vocab=f36e8346
-/
theorem sumSquaresColumnMinors_pos_of_rank_mul_eq
    {κ : Type*} [Fintype κ]
    (A : Matrix (Fin n) ι ℝ) (B : Matrix ι κ ℝ)
    (hAB : (A * B).rank = n) :
    0 < sumSquaresColumnMinors A := by
  classical
  obtain ⟨c, hc⟩ := exists_column_minor_of_rank_mul_eq A B hAB
  unfold sumSquaresColumnMinors
  exact (sq_pos_of_ne_zero hc).trans_le
    (Finset.single_le_sum (fun (b : Fin n ↪ ι) _ => sq_nonneg ((A.submatrix id b).det))
      (Finset.mem_univ c))

end AbelFormalization
