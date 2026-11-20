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

/--
@isnad1 id=mem.1h5v.s5.ff4f80866c5f from=translated src=- shape=9d988103 vocab=a48eb0c2
-/
theorem pathConfigurationDisplacement_mem_latticeBall {n k r : ℕ}
    {C A : Configuration (Fin n) k} (hA : A ∈ pathConfigurationBall C r) :
    pathConfigurationDisplacement C A ∈ latticeBall k r := by
  change ∑ i, Int.natAbs (pathConfigurationDisplacement C A i) ≤ r
  simpa only [pathConfigurationDisplacement, pathConfigurationBall, Set.mem_ofPred_eq,
    pathConfigurationDist, natDist_eq_natAbs_intSub] using hA

/--
@isnad1 id=injectiv.0h3v.s4.e618e8aa3daa from=translated src=- shape=5a3f3fa5 vocab=a0f9189d
-/
theorem pathConfigurationDisplacement_injective {n k : ℕ}
    (C : Configuration (Fin n) k) :
    Function.Injective (pathConfigurationDisplacement C) := by
  intro A B hAB
  apply (configurationEquivOrderEmbedding (Fin n) k).injective
  ext i
  have hi := congrFun hAB i
  simp only [pathConfigurationDisplacement, coordinate] at hi
  omega

/-- Every explicit path-configuration ball is bounded by the exact ambient lattice-ball count.
@isnad1 id=le.0h4v.s4.9401df121021 from=translated src=- shape=6bacb66d vocab=e8cbeb54
-/
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
