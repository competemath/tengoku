import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.Automorphisms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof transport for all source-coordinate and finite-witness obligations

The seven representation fields of `Result` are parameters here; they are
supplied by `AlbertLean.TauCetiBridge`.  Every remaining field is transported
from the completed coordinate proof, never from the old challenge placeholder.
-/

noncomputable section
namespace CompactOneBit

local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)

end CompactOneBit
