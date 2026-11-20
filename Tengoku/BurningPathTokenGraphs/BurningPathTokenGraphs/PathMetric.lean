import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TokenGraph
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Int.NatAbs
import Tengoku.Seed.Data.Nat.Dist

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordered-coordinate metric for path-token configurations

The graph-distance theorem will identify this explicitly defined `ℓ₁` distance with the distance
in `pathTokenGraph`.
-/

open scoped BigOperators

namespace BurningPath

/-- The `i`-th occupied vertex of a path-token configuration, in increasing order.-/
noncomputable def coordinate {n k : ℕ} (A : Configuration (Fin n) k) (i : Fin k) : Fin n :=
  configurationEquivOrderEmbedding (Fin n) k A i

theorem coordinate_strictMono {n k : ℕ} (A : Configuration (Fin n) k) :
    StrictMono (coordinate A) :=
  (configurationEquivOrderEmbedding (Fin n) k A).strictMono

/-- The ordered-coordinate `ℓ₁` distance occurring in the path-token metric formula.-/
noncomputable def pathConfigurationDist {n k : ℕ}
    (A B : Configuration (Fin n) k) : ℕ :=
  ∑ i : Fin k, Nat.dist (coordinate A i).val (coordinate B i).val

@[simp]
theorem pathConfigurationDist_self {n k : ℕ} (A : Configuration (Fin n) k) :
    pathConfigurationDist A A = 0 := by
  simp [pathConfigurationDist]

theorem pathConfigurationDist_comm {n k : ℕ} (A B : Configuration (Fin n) k) :
    pathConfigurationDist A B = pathConfigurationDist B A := by
  simp only [pathConfigurationDist, Nat.dist_comm]

theorem pathConfigurationDist_triangle {n k : ℕ}
    (A B C : Configuration (Fin n) k) :
    pathConfigurationDist A C ≤ pathConfigurationDist A B + pathConfigurationDist B C := by
  simp only [pathConfigurationDist, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ Nat.dist.triangle_inequality _ _ _

theorem pathConfigurationDist_eq_zero_iff {n k : ℕ}
    (A B : Configuration (Fin n) k) :
    pathConfigurationDist A B = 0 ↔ A = B := by
  constructor
  · intro h
    apply (configurationEquivOrderEmbedding (Fin n) k).injective
    ext i
    exact Nat.eq_of_dist_eq_zero <|
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ Nat.zero_le _).mp h i (Finset.mem_univ i)
  · rintro rfl
    exact pathConfigurationDist_self A

/-- Natural distance is the natural absolute value of the corresponding integer difference.-/
theorem natDist_eq_natAbs_intSub (a b : ℕ) :
    Nat.dist a b = ((a : ℤ) - b).natAbs := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Int.natAbs_natCast_sub_natCast_of_le hab]
  · rw [Nat.dist_eq_sub_of_le_right hba, Int.natAbs_natCast_sub_natCast_of_ge hba]

end BurningPath
