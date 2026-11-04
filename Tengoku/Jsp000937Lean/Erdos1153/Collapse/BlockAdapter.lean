import Tengoku.Jsp000937Lean.Erdos1153.Collapse.Block
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Package

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary-cardinality wrapper for block localization

The core collapse theorem is naturally parameterized by a full array of
cardinality `q+2` and a block pattern with `d+2` nodes.  Dense-block
applications instead begin with arbitrary cardinalities `n,m` together with
proofs `2 ≤ n` and `2 ≤ m`.  This file performs exactly those two
reparameterizations, dispatches the four placements, and exposes the global
gap index as `block.start + g.val`.
-/

namespace Erdos1153
namespace Collapse

open Erdos1153.DeBoorPinkus

noncomputable section

namespace ConsecutiveBlock

/-- The global nodal gap corresponding to a local gap of a consecutive
block.-/
def gapIndex {n m : ℕ} (block : ConsecutiveBlock n m)
    (g : Fin (m - 1)) : Fin (n - 1) :=
  ⟨block.start + g.val, by
    have hg := g.isLt
    have hfit := block.fits
    omega⟩

@[simp]
lemma gapIndex_val {n m : ℕ} (block : ConsecutiveBlock n m)
    (g : Fin (m - 1)) :
    (block.gapIndex g).val = block.start + g.val :=
  rfl

end ConsecutiveBlock

end

end Collapse
end Erdos1153
