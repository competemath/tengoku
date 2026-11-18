import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Orthogonality
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.SimpleDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characters determine finite-dimensional representations

Over an algebraically closed field of characteristic zero, two finite-dimensional
representations of a finite group are isomorphic if and only if their characters
are equal.

The proof decomposes both representations into finite biproducts of simple
representations, uses Schur orthogonality to compare the multiplicities of each
simple summand, and then reindexes the resulting biproducts.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace FDRep

universe u v

variable {k : Type u} {G : Type u} [Field k] [Group G]

end FDRep
