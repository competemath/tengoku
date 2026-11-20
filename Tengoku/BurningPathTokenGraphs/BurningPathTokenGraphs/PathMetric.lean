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

/--
@isnad1 id=strictmo.0h3v.s4.9e8653389d55 from=translated src=- shape=5268e410 vocab=50ca0ae5
-/
theorem coordinate_strictMono {n k : ℕ} (A : Configuration (Fin n) k) :
    StrictMono (coordinate A) :=
  (configurationEquivOrderEmbedding (Fin n) k A).strictMono

/-- The ordered-coordinate `ℓ₁` distance occurring in the path-token metric formula.-/
noncomputable def pathConfigurationDist {n k : ℕ}
    (A B : Configuration (Fin n) k) : ℕ :=
  ∑ i : Fin k, Nat.dist (coordinate A i).val (coordinate B i).val

/--
@isnad1 id=eq.0h3v.s4.cb56f22097be from=translated src=- shape=703bece1 vocab=24b9e557
-/
@[simp]
theorem pathConfigurationDist_self {n k : ℕ} (A : Configuration (Fin n) k) :
    pathConfigurationDist A A = 0 := by
  simp [pathConfigurationDist]

/--
@isnad1 id=eq.0h4v.s4.38500e471677 from=translated src=- shape=825885f6 vocab=24b9e557
-/
theorem pathConfigurationDist_comm {n k : ℕ} (A B : Configuration (Fin n) k) :
    pathConfigurationDist A B = pathConfigurationDist B A := by
  simp only [pathConfigurationDist, Nat.dist_comm]

/--
@isnad1 id=le.0h5v.s5.0ce3ad9c6c7f from=translated src=- shape=462184ee vocab=ea8d268d
-/
theorem pathConfigurationDist_triangle {n k : ℕ}
    (A B C : Configuration (Fin n) k) :
    pathConfigurationDist A C ≤ pathConfigurationDist A B + pathConfigurationDist B C := by
  simp only [pathConfigurationDist, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ Nat.dist.triangle_inequality _ _ _

/--
@isnad1 id=iff.0h4v.s5.b99a34ba82dd from=translated src=- shape=7fa9cc7e vocab=24b9e557
-/
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

/-- Natural distance is the natural absolute value of the corresponding integer difference.
@isnad1 id=eq.0h2v.s4.94bb5c0e8440 from=translated src=- shape=8d1aeb36 vocab=86cde8e0
-/
theorem natDist_eq_natAbs_intSub (a b : ℕ) :
    Nat.dist a b = ((a : ℤ) - b).natAbs := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Int.natAbs_natCast_sub_natCast_of_le hab]
  · rw [Nat.dist_eq_sub_of_le_right hba, Int.natAbs_natCast_sub_natCast_of_ge hba]

end BurningPath
