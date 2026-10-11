import Tengoku.OpenaiMath.OAI.Geometry.ConjugatePoints.Distance
import Tengoku.OpenaiMath.OAI.Geometry.ConjugatePoints.Convexity
import Tengoku.OpenaiMath.OAI.Geometry.ConjugatePoints.FundamentalGroup
import Tengoku.OpenaiMath.OAI.Geometry.ConjugatePoints.NoConjugatePoints

namespace OAI

noncomputable section

/-!
# The universal-cover shear obstruction and the three-manifold existence theorem.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open GluedConstruction HyperbolicCore LoopTopology RiemannianCoordinates
lemma lowPoint_clip : height (projection lowPoint) ≤ Real.log 4 := by
  rw [height_projection_high (by norm_num [lowPoint])]
  exact (Real.log_lt_log (by norm_num [lowPoint]) (by norm_num [lowPoint] : lowPoint.im < 4)).le
lemma blockMap_low (i : Bool) (t : ℝ) :
    blockMap i (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle)) =
      inclusion i (pieceFiber lowPoint lowPoint_core t) := by
  change inclusion i (clippedPiece (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle))) = _
  rw [clippedPiece_fixed _ lowPoint_clip]
  rfl
lemma compact_fiber_periodic (i : Bool) :
    (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 1 =
      (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 0 := by
  apply congrArg (inclusion i)
  apply Prod.ext
  · rfl
  · change ((6*(1:ℝ) : ℝ) : GluedConstruction.Circle) = ((6*(0:ℝ) : ℝ) : GluedConstruction.Circle)
    simp

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.LoopTopology
variable {X : Type} [TopologicalSpace X]
def groupBasepointEq {x y : X} (h : x = y) : FundamentalGroup X x ≃* FundamentalGroup X y := by
  subst y
  exact MulEquiv.refl _
end ThreeManifold.LoopTopology
namespace ThreeManifold.CompactMetric
open GluedConstruction RiemannianCoordinates LoopTopology

end ThreeManifold.CompactMetric
end

namespace ThreeManifold
open Set GluedConstruction CompactMetric

end ThreeManifold

end

end OAI
