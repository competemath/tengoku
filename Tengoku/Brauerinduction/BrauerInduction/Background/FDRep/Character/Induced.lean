import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.CoindBasis
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Induced
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Induced
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Characters of induced and coinduced representations

This file relates representation-theoretic induction and coinduction to
induction of class functions.

The main representation-theoretic calculation computes the character of a
coinduced representation as a sum over right cosets, using the explicit basis
from `FDRep.CoindBasis`. Together with the induction/coinduction isomorphism,
this proves that induction of the character of a representation agrees with
the character of the induced representation.

-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

namespace FDRep

open CategoryTheory

section Coinduced

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

end Coinduced
end FDRep

namespace Tengoku.Brauerinduction.ClassFun

section InducedCharacter

variable {k G : Type u}
variable [Field k] [Group G] [Finite G]

end InducedCharacter

end Tengoku.Brauerinduction.ClassFun

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

end FDRep
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
