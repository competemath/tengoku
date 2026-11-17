import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Four-position cluster weights

The operator weights `s = (1, 0, -1, 0)` and vector weights `w = (1, -1, 1, -1)` on a
four-point cluster, from Appendix B before Lemma B.11. Each has total zero, and the
products `s_i w_j` sum to zero over each of the patterns `i < j`, `i = j`, `i > j`.
The identities hold over every commutative ring.
-/

namespace AlternatingAnalytic

variable {R : Type*} [CommRing R]

/-- Weights for the operator position in a four-element cluster.-/
def clusterOperatorWeight : Fin 4 → R := ![1, 0, -1, 0]

/-- Weights for the vector position in a four-element cluster.-/
def clusterVectorWeight : Fin 4 → R := ![1, -1, 1, -1]

/-- The operator weights have total weight zero.-/
theorem sum_clusterOperatorWeight : ∑ i : Fin 4, clusterOperatorWeight (R := R) i = 0 := by
  norm_num [Fin.sum_univ_succ, clusterOperatorWeight]

/-- The vector weights have total weight zero.-/
theorem sum_clusterVectorWeight : ∑ i : Fin 4, clusterVectorWeight (R := R) i = 0 := by
  norm_num [Fin.sum_univ_succ, clusterVectorWeight]

/-- The products of the two weights cancel on the equal-position pattern.-/
theorem sum_cluster_weights_mul :
    ∑ i : Fin 4, clusterOperatorWeight (R := R) i * clusterVectorWeight i = 0 := by
  norm_num [Fin.sum_univ_succ, clusterOperatorWeight, clusterVectorWeight]

/-- The products cancel when the operator position precedes the vector position.-/
theorem sum_cluster_weights_mul_lt :
    ∑ i : Fin 4, ∑ j : Fin 4 with i < j,
      clusterOperatorWeight (R := R) i * clusterVectorWeight j = 0 := by
  simp only [Finset.sum_filter, Fin.sum_univ_four, Fin.lt_def, Fin.coe_ofNat_eq_mod]
  norm_num [clusterOperatorWeight, clusterVectorWeight, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The products cancel when the operator position follows the vector position.-/
theorem sum_cluster_weights_mul_gt :
    ∑ i : Fin 4, ∑ j : Fin 4 with j < i,
      clusterOperatorWeight (R := R) i * clusterVectorWeight j = 0 := by
  simp only [Finset.sum_filter, Fin.sum_univ_four, Fin.lt_def, Fin.coe_ofNat_eq_mod]
  norm_num [clusterOperatorWeight, clusterVectorWeight, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The product of the first weights is one.-/
@[simp] theorem cluster_weights_mul_zero :
    clusterOperatorWeight (R := R) 0 * clusterVectorWeight 0 = 1 := by
  simp [clusterOperatorWeight, clusterVectorWeight]

/-- The six weight identities, collected.-/
theorem cluster_weight_identities :
    (∑ i : Fin 4, clusterOperatorWeight (R := R) i) = 0 ∧
    (∑ i : Fin 4, clusterVectorWeight (R := R) i) = 0 ∧
    (∑ i : Fin 4, clusterOperatorWeight (R := R) i * clusterVectorWeight i) = 0 ∧
    (∑ i : Fin 4, ∑ j : Fin 4 with i < j,
      clusterOperatorWeight (R := R) i * clusterVectorWeight j) = 0 ∧
    (∑ i : Fin 4, ∑ j : Fin 4 with j < i,
      clusterOperatorWeight (R := R) i * clusterVectorWeight j) = 0 ∧
    clusterOperatorWeight (R := R) 0 * clusterVectorWeight 0 = 1 := by
  exact ⟨sum_clusterOperatorWeight, sum_clusterVectorWeight, sum_cluster_weights_mul,
    sum_cluster_weights_mul_lt, sum_cluster_weights_mul_gt, cluster_weights_mul_zero⟩

/-- A coefficient depending only on the three relative-order patterns cancels.-/
theorem sum_cluster_weights_order_pattern (a b c : R) :
    ∑ i : Fin 4, ∑ j : Fin 4,
      clusterOperatorWeight (R := R) i * clusterVectorWeight j *
        (if i < j then a else if i = j then b else c) = 0 := by
  simp only [Fin.sum_univ_four, Fin.lt_def, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  norm_num [clusterOperatorWeight, clusterVectorWeight, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

end AlternatingAnalytic
