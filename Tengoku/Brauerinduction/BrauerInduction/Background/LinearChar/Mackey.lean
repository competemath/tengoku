import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Mackey.Character
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.Eigenspace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mackey theory for induced linear characters

This file specializes the Mackey character computation to representations
induced from inertia groups of linear characters.

Let `A` be an abelian normal subgroup of `G`, let `ψ : A →* kˣ`, and let
`I` be the inertia subgroup of `ψ`. If a representation `σ` of `I` embeds into
the `ψ`-eigenspace of a representation `ρ`, then all Mackey terms outside the
identity double coset vanish. Consequently the endomorphism ring of
`Ind_I^G σ` has dimension one when `σ` is simple.
-/

open CategoryTheory BigOperators

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

end FDRep
