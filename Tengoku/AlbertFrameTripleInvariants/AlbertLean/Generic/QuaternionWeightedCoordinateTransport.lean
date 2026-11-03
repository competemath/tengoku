import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCommonPlaneAutAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms coordinate_transport` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
variable {K : Type*} [Field K] [CharZero K]

/-- Coordinate conjugacy is transported back to the original six-space.-/
theorem coordinate_transport
    (L L' : Vec6 K ≃ₗ[K] Vec6 K) (P Q : Vec6 K →ₗ[K] Vec6 K)
    (S T : Mat2 K)
    (hcoord : (commonPlaneMap S).comp
      ((coordinateConjugate L P).comp (commonPlaneMap T)) = coordinateConjugate L' Q) :
    (L'.toLinearMap.comp ((commonPlaneMap S).comp L.symm.toLinearMap)).comp
      (P.comp (L.toLinearMap.comp
        ((commonPlaneMap T).comp L'.symm.toLinearMap))) = Q := by
  apply LinearMap.ext
  intro x
  change L' ((commonPlaneMap S)
    (L.symm (P (L ((commonPlaneMap T) (L'.symm x)))))) = Q x
  have hx := congrArg L' (LinearMap.congr_fun hcoord (L'.symm x))
  change L' ((commonPlaneMap S)
      (L.symm (P (L ((commonPlaneMap T) (L'.symm x)))))) =
    L' (L'.symm (Q (L' (L'.symm x)))) at hx
  simpa only [L'.apply_symm_apply] using hx

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
