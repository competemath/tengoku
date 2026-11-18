import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.InducedCharacter
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Iso
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.CoindBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of induced linear characters through quotients

This file contains compatibility results for induced linear characters under
quotient maps, especially when a linear character is pulled back along a
quotient.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

namespace FDRep

open BigOperators

end FDRep
