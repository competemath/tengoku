import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ProductLaws
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceFormLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem traceFormAssociative (x y z : Coord) :
    traceForm (structuredProduct x y) z =
      traceForm x (structuredProduct y z) := by
  rw [structuredProduct_eq_productForm,
    structuredProduct_eq_productForm,
    traceForm_eq_gram, traceForm_eq_gram]
  simp [traceFormGram, productForm, v, q]
  ring

end AlbertLean
