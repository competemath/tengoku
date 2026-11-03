import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ProductLaws
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceFormLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s3.da6832744ee2 from=translated src=- shape=b70c6bb1 vocab=5a01502b
-/
theorem productTrace_eq_traceN (x : Coord) : productTrace x = traceN x := by
  simp_rw [productTrace, leftMulMatrixTrace, structuredProduct_eq_productForm]
  simp [productForm, basisVec, traceN_eq_coords, v, q, Fin.sum_univ_succ]
  ring

end AlbertLean
