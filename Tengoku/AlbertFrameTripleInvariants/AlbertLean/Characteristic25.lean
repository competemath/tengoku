import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceFormLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

/-- Coordinate 25 of the original characteristic identity.-/
theorem characteristicCoordinate25 (x : Coord) :
    (structuredProduct x (structuredProduct x x) -
      traceN x • structuredProduct x x + spurN x • x -
      cubicNorm x • one) (25 : Fin 27) = 0 := by
  simp_rw [structuredProduct_eq_productForm]
  simp [productForm, traceN_eq_coords, spurN_eq_spurPairForm, spurPairForm,
    cubicNorm, one, v, q]
  ring

end AlbertLean
