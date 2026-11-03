import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceFormLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

/-- Coordinate 6 of the original characteristic identity.
@isnad1 id=eq.0h1v.s6.dc217a57e655 from=translated src=- shape=98e49c1d vocab=24140918
-/
theorem characteristicCoordinate06 (x : Coord) :
    (structuredProduct x (structuredProduct x x) -
      traceN x • structuredProduct x x + spurN x • x -
      cubicNorm x • one) (6 : Fin 27) = 0 := by
  simp_rw [structuredProduct_eq_productForm]
  simp [productForm, traceN_eq_coords, spurN_eq_spurPairForm, spurPairForm,
    cubicNorm, one, v, q]
  ring

end AlbertLean
