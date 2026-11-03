import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.All

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

/-- The structured Springer product agrees with the exact frozen C0 tensor evaluator.
@isnad1 id=eq.0h2v.s3.8edd216b9a01 from=translated src=- shape=6c8684e5 vocab=6342cc0a
-/
theorem structuredProduct_eq_tensor (x y : Coord) :
    structuredProduct x y = tensorProduct x y :=
  (structuredProduct_eq_productForm x y).trans
    (tensorProduct_eq_productForm x y).symm

end AlbertLean
