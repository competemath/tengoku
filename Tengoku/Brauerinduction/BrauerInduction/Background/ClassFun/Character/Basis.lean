import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basis
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Orthogonality
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Orthogonality
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Span
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.ConjClasses

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Bases of class functions from irreducible characters

This file proves that the irreducible characters of a finite group form a basis
of its space of class functions over an algebraically closed field of
characteristic zero.

Linear independence follows from Schur orthogonality. Spanning is proved by
duality. A linear functional vanishing on the span of the irreducible characters
is represented, via the nondegenerate character pairing, by pairing with a class
function `f`. The vanishing of the functional on all irreducible characters says
that `f` is orthogonal to every irreducible character; the theorem
`classFun_eq_zero_of_orthogonal_simples` then gives `f = 0`. Thus the dual
annihilator of the span is zero, and finite-dimensionality implies that the span
is the whole space.

The file then constructs a basis consisting of irreducible characters, shows
that the associated simple representations form a complete set of
isomorphism-class representatives, and deduces that the dimension of the
class-function space equals the number of irreducible representations.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v w

namespace Tengoku.Brauerinduction.ClassFun

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} {G : Type v}
variable [Field k] [Group G]

/--
A basis of the class-function space consisting of characters of simple
representations.-/
structure IrrepCharBasis
    (k : Type u) (G : Type v)
    [Field k] [Group G] where
  /-- The index type of the chosen basis.-/
  ι : Type (max u v)

  /-- The index type is finite.-/
  [fintype : Fintype ι]

  /-- The simple representations indexing the basis.-/
  V : ι → FDRep k G

  /-- Each representation in the family is simple.-/
  simple : ∀ i, Simple (V i)

  /-- The corresponding basis of class functions.-/
  b : Module.Basis ι k (ClassFun k G)

  /-- Each basis vector is the character of its corresponding representation.-/
  b_eq : ∀ i, b i = ClassFun.character (V i)

attribute [instance] IrrepCharBasis.fintype

end Tengoku.Brauerinduction.ClassFun

namespace FDRep

end FDRep
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
