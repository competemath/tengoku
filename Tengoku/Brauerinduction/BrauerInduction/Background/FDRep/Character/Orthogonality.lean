import Tengoku.Seed.RingTheory.SimpleModule.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.Rep.Invariants
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Simple

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Orthogonality of irreducible characters

This file proves the Schur orthogonality relation for characters of simple
objects of `FDRep`.

The scalar product is written algebraically as

`|G|⁻¹ * ∑ g, χ_V(g) * χ_W(g⁻¹)`,

which avoids complex conjugation and works over an algebraically closed field of
characteristic zero.
-/

open CategoryTheory CategoryTheory.Limits BigOperators

namespace FDRep

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]

end FDRep
