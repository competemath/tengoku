import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedBlockActionAttachment
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedFirstProjectorMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms commonPlaneMap_comm_standardProjector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms commonPlaneMap_comm_weightedFirst` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
variable {K : Type*} [Field K] [CharZero K]

/-- A common plane change preserves every labelled first-frame plane.
@isnad1 id=eq.0h3v.s9.e9bb40e593e1 from=translated src=- shape=1338b1fd vocab=b21be29f
-/
theorem commonPlaneMap_comm_standardProjector (T : Mat2 K) (i : Fin 3) :
    (commonPlaneMap T).comp (standardProjector i) =
      (standardProjector i).comp (commonPlaneMap T) := by
  apply LinearMap.ext
  intro x
  funext q
  rcases q with q | q <;> by_cases hqi : q = i <;>
    simp [commonPlaneMap, standardProjector, coordinateLabel, hqi]

/-- The weighted first projector is scalar on the common two-dimensional
factor, hence commutes with every common plane change.
@isnad1 id=eq.0h3v.s9.efa1413e1e11 from=translated src=- shape=1ae3b818 vocab=3c9bfa3f
-/
theorem commonPlaneMap_comm_weightedFirst (T : Mat2 K) (p : Fin 3 → K) :
    (commonPlaneMap T).comp (weightedFirstAction p) =
      (weightedFirstAction p).comp (commonPlaneMap T) := by
  apply LinearMap.ext
  intro x
  funext q
  rcases q with q | q <;>
    simp [commonPlaneMap, weightedFirstAction, LinearMap.comp_apply,
      Fin.sum_univ_three] <;> ring

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
