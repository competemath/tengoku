import Tengoku.Jsp000958Lean.Randy1153.Collapse.Block
import Tengoku.Jsp000958Lean.Randy1153.DeBoorPinkus.Package

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

namespace Randy1153
namespace Collapse

open Randy1153.DeBoorPinkus

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

/--
@isnad1 id=eq.0h4v.s6.417dfb82dad9 from=translated src=- shape=448f57e0 vocab=ed8f43ae
-/
@[simp]
lemma gapIndex_val {n m : ℕ} (block : ConsecutiveBlock n m)
    (g : Fin (m - 1)) :
    (block.gapIndex g).val = block.start + g.val :=
  rfl

end ConsecutiveBlock

end

end Collapse
end Randy1153
