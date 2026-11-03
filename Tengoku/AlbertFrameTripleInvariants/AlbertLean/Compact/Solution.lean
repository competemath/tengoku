import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.CoordinateProof
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TauCetiBridge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ModelProduct
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The proved rational-example presentation

This supporting presentation is retained by the proof development; see
`Definitions.lean` for its relationship to the selected public statement. -/

noncomputable section
namespace CompactOneBit

local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)

end CompactOneBit
