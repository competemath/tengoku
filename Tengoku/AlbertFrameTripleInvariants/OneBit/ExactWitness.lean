import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Solution
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ModelProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The rational example: the short entry point

`exactWitness` restates, without change, the historical bundle `AlbertLean.solution`:
the two rational configurations are lawful frame triples, all 27 pair and 27 (centred)
triple traces agree, the two detector values differ, and no unital ℚ-linear automorphism
of the coordinate algebra transports one configuration to the other. It does not import
the generic theorem. The coordinates, the multiplication conventions and an exact
arithmetic check are in `examples/exact-witness/README.md`.

This is a supporting result, not one of the five theorems selected in `comparator.json`;
the selected form of the same example is `OneBit.rationalWitness`, and the relabelling
strengthening is `OneBit.rationalWitness_not_equivalent_under_relabelling`. The
historical `AlbertLean.challenge` (a `sorry` placeholder) is not used here.
-/

namespace OneBit

/-- The complete existing finite witness result, exposed without additional hypotheses.-/
theorem exactWitness : AlbertLean.CombinedTarget := AlbertLean.solution

end OneBit
