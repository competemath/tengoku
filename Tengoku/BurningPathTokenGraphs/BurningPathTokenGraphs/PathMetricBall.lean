import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.LatticeBall
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Balls for the ordered-coordinate path-token metric

Translation by a fixed center embeds every configuration ball into the ambient integer `ℓ₁` ball.
-/

namespace BurningPath

/-- The ball for the explicit ordered-coordinate distance.-/
def pathConfigurationBall {n k : ℕ} (C : Configuration (Fin n) k) (r : ℕ) :
    Set (Configuration (Fin n) k) :=
  {A | pathConfigurationDist A C ≤ r}

/-- Coordinatewise displacement from a fixed path-token configuration.-/
noncomputable def pathConfigurationDisplacement {n k : ℕ}
    (C A : Configuration (Fin n) k) : Fin k → ℤ :=
  fun i ↦ ((coordinate A i).val : ℤ) - (coordinate C i).val

theorem pathConfigurationDisplacement_mem_latticeBall {n k r : ℕ}
    {C A : Configuration (Fin n) k} (hA : A ∈ pathConfigurationBall C r) :
    pathConfigurationDisplacement C A ∈ latticeBall k r := by
  change ∑ i, Int.natAbs (pathConfigurationDisplacement C A i) ≤ r
  simpa only [pathConfigurationDisplacement, pathConfigurationBall, Set.mem_ofPred_eq,
    pathConfigurationDist, natDist_eq_natAbs_intSub] using hA

theorem pathConfigurationDisplacement_injective {n k : ℕ}
    (C : Configuration (Fin n) k) :
    Function.Injective (pathConfigurationDisplacement C) := by
  intro A B hAB
  apply (configurationEquivOrderEmbedding (Fin n) k).injective
  ext i
  have hi := congrFun hAB i
  simp only [pathConfigurationDisplacement, coordinate] at hi
  omega

/-- Every explicit path-configuration ball is bounded by the exact ambient lattice-ball count.-/
theorem pathConfigurationBall_ncard_le {n k : ℕ}
    (C : Configuration (Fin n) k) (r : ℕ) :
    (pathConfigurationBall C r).ncard ≤ latticeBallPolynomial k r := by
  calc
    (pathConfigurationBall C r).ncard ≤ (latticeBall k r).ncard := by
      exact Set.ncard_le_ncard_of_injOn (pathConfigurationDisplacement C)
        (fun A hA ↦ pathConfigurationDisplacement_mem_latticeBall hA)
        (pathConfigurationDisplacement_injective C).injOn (latticeBall_finite k r)
    _ = latticeBallPolynomial k r := latticeBall_ncard k r

end BurningPath
