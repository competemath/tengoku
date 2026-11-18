import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.Induced
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Induced

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Character formulas for induced linear characters

This file gives character formulas for `FDRep.indLin` and `FDRep.coindLin`.
The proofs are consequences of the generic character formula for induced
representations.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

open BigOperators

/--
Induced and coinduced linear representations have the same character.
@isnad1 id=eq.0h4v.s7.62ffbce76a88 from=translated src=- shape=d6772bd0 vocab=a748cbcf
-/
lemma char_indLin_eq_char_coindLin
    (H : Subgroup G) (ψ : H →* kˣ) :
    (FDRep.indLin H ψ).character =
      (FDRep.coindLin H ψ).character := by
  exact FDRep.char_eq_of_iso
    (FDRep.indLinCoindLinIso H ψ)

end FDRep

namespace Tengoku.Brauerinduction.ClassFun

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
