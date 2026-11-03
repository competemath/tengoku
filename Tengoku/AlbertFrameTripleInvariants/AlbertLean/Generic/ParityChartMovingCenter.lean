import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamilyInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms curveOmega_pf` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms movingCenter_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms moved_r` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Moving reflection centers into the parity chart

The coordinate calculation supports the representation of even actions by
the fixed-parity rational family. It identifies the eight coefficients
of the moving-center expression with the eight coordinates, up to signs.
-/
noncomputable section
namespace AlbertLean.Triality.ParityChartMovingCenter

open ExteriorSix CoordinateTensor StructuredCubic
open SourceVectorPairDephase SourceEvenReflections RationalEvenFamily

universe u
variable {K : Type u} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

def curveOmega (t : K) : ExteriorSix.W K
  | .i12 => t
  | .i13 => t ^ 2
  | .i14 => t ^ 3
  | .i23 => t ^ 4
  | .i24 => t ^ 5
  | .i34 => t ^ 6

/--
@isnad1 id=eq.0h2v.s5.869161e60936 from=translated src=- shape=8e89c0bf vocab=584b2b75
-/
theorem curveOmega_pf (t : K) : Pf (curveOmega t) = t ^ 7 := by
  rw [pf_coordinate]
  simp only [curveOmega]
  ring

def movingCenter (t : K) : VCoord K := center 1 1 (curveOmega t) 1

/--
@isnad1 id=eq.0h2v.s5.7be7a5ce3ed5 from=translated src=- shape=e224aef9 vocab=9c91a835
-/
theorem movingCenter_norm (t : K) : nV (movingCenter t) = 1 := by
  rw [movingCenter, norm_center 1 1 (curveOmega t) 1 (by norm_num)]
  norm_num

/--
@isnad1 id=eq.0h2v.s5.f3beca66a254 from=translated src=- shape=e224aef9 vocab=003695de
-/
@[simp] theorem movingCenter_r (t : K) : (movingCenter t).r = 1 := rfl

/-- The eight coefficients recover the eight coordinates of A, up to signs.-/
def pivotValue (A : VCoord K) (t : K) : K :=
  A.r * t ^ 7 - A.z - A.omega .i34 * t + A.omega .i24 * t ^ 2 -
    A.omega .i23 * t ^ 3 - A.omega .i14 * t ^ 4 +
    A.omega .i13 * t ^ 5 - A.omega .i12 * t ^ 6

/--
@isnad1 id=eq.0h3v.s5.edd6a2887a0c from=translated src=- shape=b546590f vocab=f1918805
-/
theorem moved_r (A : VCoord K) (t : K) :
    (evenV parityVector (movingCenter t) A).r = pivotValue A t := by
  simp only [evenV, reflectV]
  change (A.r - (BV (movingCenter t) A / nV (movingCenter t)) *
      (movingCenter t).r) -
      (BV parityVector (reflectV (movingCenter t) A) / nV parityVector) *
        parityVector.r = pivotValue A t
  rw [movingCenter_norm, movingCenter_r]
  simp only [parityVector, mul_zero, sub_zero, div_one, mul_one]
  simp only [BV, BW, movingCenter, center, one_pow, div_one, curveOmega]
  rw [curveOmega_pf]
  unfold pivotValue
  ring

end AlbertLean.Triality.ParityChartMovingCenter
