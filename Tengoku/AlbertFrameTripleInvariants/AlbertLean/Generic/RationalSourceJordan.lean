import Tengoku.AlbertFrameTripleInvariants.AlbertLean.JordanLaws
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.StructuredProductF0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceJordanIdentity_rat` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The Jordan identity in rational structured coordinates

Transport the rational `Coord` identity through the product-preserving
linear equivalence `structuredEquiv`, without expanding coordinates.
-/

namespace AlbertLean.Comparison.RationalSourceJordan

open AlbertLean
open AlbertLean.Triality
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Comparison.StructuredProductF0

theorem sourceJordanIdentity_rat (x y : JCoord ℚ) :
    sourceProduct (sourceProduct x y) (sourceProduct x x) =
      sourceProduct x (sourceProduct y (sourceProduct x x)) := by
  apply structuredEquiv.injective
  calc
    structuredEquiv
        (sourceProduct (sourceProduct x y) (sourceProduct x x)) =
        structuredProduct (structuredEquiv (sourceProduct x y))
          (structuredEquiv (sourceProduct x x)) :=
      StructuredSourceProductAgreesWithF0 _ _
    _ = structuredProduct
          (structuredProduct (structuredEquiv x) (structuredEquiv y))
          (structuredProduct (structuredEquiv x) (structuredEquiv x)) := by
      rw [StructuredSourceProductAgreesWithF0,
        StructuredSourceProductAgreesWithF0]
    _ = structuredProduct (structuredEquiv x)
          (structuredProduct (structuredEquiv y)
            (structuredProduct (structuredEquiv x) (structuredEquiv x))) :=
      AlbertLean.jordanIdentity (structuredEquiv x) (structuredEquiv y)
    _ = structuredProduct (structuredEquiv x)
          (structuredEquiv (sourceProduct y (sourceProduct x x))) := by
      rw [StructuredSourceProductAgreesWithF0,
        StructuredSourceProductAgreesWithF0]
    _ = structuredEquiv
          (sourceProduct x (sourceProduct y (sourceProduct x x))) :=
      (StructuredSourceProductAgreesWithF0 _ _).symm

end AlbertLean.Comparison.RationalSourceJordan
